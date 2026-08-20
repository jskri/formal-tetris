//! Text-entry fields (name/code fields on the lobby screens) and the
//! out-of-band clipboard exchange used to pass connection codes between
//! players.

use macroquad::prelude::*;
use t1::misc::RepeatTimer;

/// spec: §15.1a. One frame's worth of text-editing input, polled **once**
/// per frame and applied only to the focused field — macroquad's
/// `get_char_pressed` drains one global queue shared by every field on
/// screen.
pub struct TextEdit {
    pub chars: Vec<char>,
    pub backspace: bool,
    pub paste: Option<String>,
    pub copy: bool,
}

/// spec: §15.1a. Backspace-hold autorepeat timing for text fields, tuned
/// independently of gameplay's own `DAS_DELAY`/`ARR` (`process_input`)
/// though it reuses `RepeatTimer`'s shape.
const BACKSPACE_DELAY: f64 = 0.35;
const BACKSPACE_ARR: f64 = 0.05;

/// Continues a Backspace hold past the first (already edge-triggered, via
/// `poll_text_edit`/`TextInput::apply`) character removal: after
/// `BACKSPACE_DELAY`, pops one more character every `BACKSPACE_ARR` for as
/// long as the key stays down. `timer` lives on the lobby, one per screen.
pub fn drive_backspace_repeat(field: &mut TextInput, timer: &mut Option<RepeatTimer>, now: f64) {
    if is_key_down(KeyCode::Backspace) {
        match timer {
            None => *timer = Some(RepeatTimer::new(now)),
            Some(t)
                if now - t.pressed_at >= BACKSPACE_DELAY && now - t.last_fire >= BACKSPACE_ARR =>
            {
                field.text.pop();
                t.last_fire = now;
            }
            Some(_) => {}
        }
    } else {
        *timer = None;
    }
}

pub fn poll_text_edit() -> TextEdit {
    let ctrl = is_key_down(KeyCode::LeftControl) || is_key_down(KeyCode::RightControl);
    let backspace = is_key_pressed(KeyCode::Backspace);
    // spec: §15.1a — Ctrl+C copies the focused field's connection code;
    // see copy_out for where the write actually lands.
    let copy = ctrl && is_key_pressed(KeyCode::C);
    let paste = if ctrl && is_key_pressed(KeyCode::V) {
        paste_in().map(|s| s.trim().to_owned())
    } else {
        None
    };
    let mut chars = Vec::new();
    while let Some(c) = get_char_pressed() {
        // Ctrl+V/Ctrl+C also deliver a bare 'v'/'c' through this same
        // character queue; drop everything typed while Ctrl is held so it
        // doesn't get appended alongside the pasted text.
        if !ctrl && is_typable(c) {
            chars.push(c);
        }
    }
    TextEdit {
        chars,
        backspace,
        paste,
        copy,
    }
}

/// `char::is_control` only covers the C0/C1 control ranges, not macOS's
/// `NSXxxFunctionKey` codepoints (arrows, Home/End, Delete, F-keys, …),
/// which Cocoa delivers through the same character stream as
/// `U+F700`–`U+F8FF`. Left unfiltered, an arrow press while a field has
/// focus would append an invisible junk character to it.
fn is_typable(c: char) -> bool {
    !c.is_control() && !('\u{F700}'..='\u{F8FF}').contains(&c)
}

/// Shared cap for every lobby name/code field (`HostLobby`/`JoinLobby`); a
/// caller wanting a different limit passes its own value to
/// `TextInput::apply` instead.
pub const NAME_FIELD_MAX_LEN: usize = 64;

#[derive(Default)]
pub struct TextInput {
    pub text: String,
}

impl TextInput {
    pub fn with(text: String) -> TextInput {
        TextInput { text }
    }

    /// Applies one frame's edit to this field, capping it at `max_len`
    /// Unicode scalar values across both typed and pasted input. Only
    /// ever called for the focused field.
    pub fn apply(&mut self, e: &TextEdit, max_len: usize) {
        if e.backspace {
            self.text.pop();
        }
        if let Some(s) = &e.paste {
            for c in s.chars() {
                if self.text.chars().count() >= max_len {
                    break;
                }
                self.text.push(c);
            }
        }
        for &c in &e.chars {
            if self.text.chars().count() < max_len {
                self.text.push(c);
            }
        }
    }

    pub fn take(&mut self) -> String {
        std::mem::take(&mut self.text)
    }
}

/// Hands `text` to the system clipboard, or, failing that, to stdout.
///
/// spec: §15.1a. Neither direction goes through miniquad's own clipboard on
/// Linux: writing is unsound on both X11 and Wayland backends independently
/// of anything this app does, and reading breaks as a consequence of
/// working around that on the write side (once `copy_out` shells out to
/// `wl-copy`, the text lands on Wayland's clipboard but this app still
/// reads through the X11 backend). `paste_in` shells out to
/// `wl-paste`/`xclip`/`xsel`, falling back to `clipboard_get` as a last
/// resort. `copy_out` has no comparable X11 fallback — X11 copy is not
/// implemented — and only shells out to `wl-copy` when `WAYLAND_DISPLAY`
/// shows a real Wayland session.
///
/// macOS shells out too, to `pbcopy`/`pbpaste`, because miniquad's own
/// `NSPasteboard` binding has been observed to fail its round trip on some
/// setups. Elsewhere miniquad's own implementation is used unchanged.
///
/// The outcome of one clipboard-write attempt. `Unavailable`/`Failed` carry
/// the tool name so `copy_to_clipboard` can name it in the status line.
// Which variants get constructed depends on target_os (below); `dead_code`
// can't see that `copy_to_clipboard`'s match on this type, compiled on every
// platform, is what actually uses them all.
#[allow(dead_code)]
enum CopyResult {
    Copied,
    /// The external program isn't installed (spawn failed).
    Unavailable(&'static str),
    /// The program ran but didn't take the text (non-zero exit, write
    /// failure, or — Windows — a read-back that didn't match).
    Failed(&'static str),
    /// Linux, no `WAYLAND_DISPLAY` — copy was never attempted (X11 write is
    /// deliberately not implemented).
    NotOnX11,
}

#[cfg(target_os = "linux")]
fn copy_out(text: &str) -> CopyResult {
    // wl-copy only (spec: §15.1a — X11 copy is not implemented), and only
    // with a real Wayland session to talk to. wl-copy daemonizes itself
    // after reading stdin, since a Wayland selection is served by its
    // owner for as long as it holds it, so `wait` returns promptly.
    if std::env::var_os("WAYLAND_DISPLAY").is_some() {
        run_clipboard_helper("wl-copy", &[], text)
    } else {
        CopyResult::NotOnX11
    }
}

#[cfg(target_os = "macos")]
fn copy_out(text: &str) -> CopyResult {
    run_clipboard_helper("pbcopy", &[], text)
}

/// Feeds `text` to `prog` on stdin. `Unavailable` if the program is absent,
/// `Failed` if it exits non-zero or the write itself fails.
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn run_clipboard_helper(prog: &'static str, args: &[&str], text: &str) -> CopyResult {
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    let Ok(mut child) = Command::new(prog)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
    else {
        return CopyResult::Unavailable(prog);
    };
    // `write_all` failing (e.g. the helper already exited) must not skip
    // `child.wait()` below — doing so would leave a zombie process behind,
    // since nothing else in this function's caller ever reaps this child.
    let write_ok = match child.stdin.take() {
        Some(mut stdin) => stdin.write_all(text.as_bytes()).is_ok(), // dropped here either way: EOF
        None => false,
    };
    let wait_ok = matches!(child.wait(), Ok(status) if status.success());
    if write_ok && wait_ok {
        CopyResult::Copied
    } else {
        CopyResult::Failed(prog)
    }
}

/// `clipboard_set` returns `()`, so a caller can't know the write landed.
/// Windows has been seen silently dropping it (while still clearing
/// whatever was there before), so read the clipboard back and compare
/// before reporting success; on mismatch, fall back to stdout.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn copy_out(text: &str) -> CopyResult {
    macroquad::miniquad::window::clipboard_set(text);
    if macroquad::miniquad::window::clipboard_get().as_deref() == Some(text) {
        CopyResult::Copied
    } else {
        CopyResult::Failed("system clipboard")
    }
}

/// spec: §15.1a. `field_name` identifies which lobby field this is ("Your
/// name", "Your code", "Host's code", "Joiner's code") for the
/// unconditional console print below — every copy is printed regardless of
/// whether `copy_out` reached the system clipboard.
pub fn copy_to_clipboard(field_name: &str, text: &str, status: &mut String) {
    println!("{field_name}: {text}");
    *status = match copy_out(text) {
        CopyResult::Copied => "Text copied to the clipboard and printed to the console.".into(),
        CopyResult::Unavailable(tool) => {
            format!("{tool} unavailable; content copied to the console.")
        }
        CopyResult::Failed(tool) => format!("{tool} failed; content copied to the console."),
        CopyResult::NotOnX11 => {
            "Copy not implemented on X11; content printed to the console.".into()
        }
    };
}

/// The read half of `copy_out`'s workaround (see its doc comment for why
/// `clipboard_get` can't be trusted on Linux once `copy_out` has put text
/// on the Wayland side). `None` covers both "not installed" and "clipboard
/// genuinely empty"; `TextEdit` treats either as nothing to paste.
#[cfg(target_os = "linux")]
fn paste_in() -> Option<String> {
    let mut candidates: Vec<(&'static str, &'static [&'static str])> = Vec::new();
    if std::env::var_os("WAYLAND_DISPLAY").is_some() {
        candidates.push(("wl-paste", &["--no-newline"]));
    }
    candidates.push(("xclip", &["-selection", "clipboard", "-o"]));
    candidates.push(("xsel", &["--clipboard", "--output"]));

    for (prog, args) in candidates {
        if let Some(text) = run_clipboard_read_helper(prog, args) {
            return Some(text);
        }
    }
    // None of the three installed: fall back to miniquad's own X11 read,
    // which still works when a real X11 application (not this one) holds
    // the selection, e.g. a terminal emulator's own copy.
    macroquad::miniquad::window::clipboard_get()
}

/// See `copy_out`'s doc comment for why macOS shells out to `pbpaste`
/// rather than trusting `clipboard_get`.
#[cfg(target_os = "macos")]
fn paste_in() -> Option<String> {
    run_clipboard_read_helper("pbpaste", &[])
}

/// Runs `prog` and captures its stdout. `None` if the program is absent,
/// exits non-zero (`wl-paste`'s own behavior on an empty Wayland
/// clipboard), or its stdout is not valid UTF-8 — every case the caller
/// should move on to the next candidate for.
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn run_clipboard_read_helper(prog: &str, args: &[&str]) -> Option<String> {
    use std::process::{Command, Stdio};

    let output = Command::new(prog)
        .args(args)
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout).ok()
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn paste_in() -> Option<String> {
    macroquad::miniquad::window::clipboard_get()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A missing helper must be reported as "did not copy", not panic and
    /// not silently pass — that verdict is what makes `copy_out` fall
    /// through to the next candidate and finally to stdout.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_missing_clipboard_helper_reports_failure() {
        assert!(
            matches!(
                run_clipboard_helper("definitely-not-a-real-clipboard-tool", &[], "ABC"),
                CopyResult::Unavailable(_)
            ),
            "an absent program must be reported as unavailable, not as having taken the text"
        );
    }

    /// spec: §15.1a — copy is never silent; the status always distinguishes
    /// success from a fallback to the console print.
    #[test]
    fn copy_status_names_the_outcome() {
        let mut status = String::new();
        copy_to_clipboard("Test field", "ABCD-EFGH", &mut status);
        assert!(!status.is_empty(), "copying must always report something");
        assert!(
            status.contains("copied to the clipboard") || status.contains("console"),
            "status must describe the outcome, got: {status}"
        );
    }

    /// A missing read helper must be reported as "nothing read," not panic
    /// — same discipline as the write side.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_missing_paste_helper_reports_nothing() {
        assert_eq!(
            run_clipboard_read_helper("definitely-not-a-real-clipboard-tool", &[]),
            None,
            "an absent program must not be reported as having produced text"
        );
    }

    /// `paste_in` must read back through the same external mechanism
    /// `copy_out` writes through, not `clipboard_get` (see `copy_out`'s doc
    /// comment). Verified with a fake `xclip` on `PATH` that answers a
    /// fixed string to `-o`, exercising the real spawn/capture path.
    #[cfg(target_os = "linux")]
    #[test]
    fn paste_reads_back_through_the_same_external_mechanism_as_copy() {
        let dir = std::env::temp_dir().join(format!("t7-fake-clipboard-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let fake_xclip = dir.join("xclip");
        std::fs::write(
            &fake_xclip,
            "#!/bin/sh
echo -n 'PASTED-CODE'
",
        )
        .unwrap();
        {
            use std::os::unix::fs::PermissionsExt as _;
            std::fs::set_permissions(&fake_xclip, std::fs::Permissions::from_mode(0o755)).unwrap();
        }

        let old_path = std::env::var("PATH").unwrap_or_default();
        // Prepend, and drop WAYLAND_DISPLAY for the duration: a real
        // Wayland session on the machine running these tests would
        // otherwise route to a real `wl-paste` before ever trying `xclip`,
        // which is a fine runtime preference but would defeat this test's
        // point of exercising the fake helper.
        let had_wayland = std::env::var_os("WAYLAND_DISPLAY");
        unsafe {
            std::env::set_var("PATH", format!("{}:{old_path}", dir.display()));
            std::env::remove_var("WAYLAND_DISPLAY");
        }
        let result = paste_in();
        unsafe {
            std::env::set_var("PATH", old_path);
            if let Some(w) = had_wayland {
                std::env::set_var("WAYLAND_DISPLAY", w);
            }
        }
        std::fs::remove_dir_all(&dir).ok();

        assert_eq!(result.as_deref(), Some("PASTED-CODE"));
    }
}
