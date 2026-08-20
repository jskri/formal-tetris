#!/usr/bin/env bash
# Registers the Tetris window icon with the desktop shell. On GNOME/Wayland
# (Ubuntu 24.04's default session) the alt-tab/taskbar icon is never taken
# from pixels an app hands over at window-creation time; GNOME looks it up
# by matching the window's app-id (set via `linux_wm_class` in
# t1/src/misc.rs's `LINUX_WM_CLASS`) against an installed .desktop file's
# StartupWMClass, then uses that file's Icon=. This script installs that
# .desktop file plus the icon it points to, for the current user only.
#
# Usage: rs/install-desktop-icon.sh [binary-name]
#   binary-name defaults to tfinal (the full game); pass e.g. t7 to point
#   the launcher at a different crate's binary instead. This only changes
#   which binary the .desktop entry's Exec runs — every tX/tfinal binary
#   shares the same app-id and so already gets the icon in alt-tab/taskbar
#   regardless of how it was started (e.g. via `cargo run`).
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bin="${1:-tfinal}"
wm_class="tetris"

icon_dir="$HOME/.local/share/icons/hicolor/scalable/apps"
apps_dir="$HOME/.local/share/applications"
mkdir -p "$icon_dir" "$apps_dir"

cp "$repo_root/assets/tetris.svg" "$icon_dir/$wm_class.svg"

target_dir="$repo_root/target/release"
[ -x "$target_dir/$bin" ] || target_dir="$repo_root/target/debug"
if [ ! -x "$target_dir/$bin" ]; then
    echo "warning: $target_dir/$bin not built yet (cargo build -p $bin); Exec= will point there anyway" >&2
fi

cat > "$apps_dir/$wm_class.desktop" <<EOF
[Desktop Entry]
Type=Application
Name=Tetris
Exec=$target_dir/$bin
Icon=$wm_class
StartupWMClass=$wm_class
Terminal=false
Categories=Game;
EOF

command -v update-desktop-database >/dev/null 2>&1 && update-desktop-database "$apps_dir" || true
command -v gtk-update-icon-cache >/dev/null 2>&1 && gtk-update-icon-cache -f -t "$HOME/.local/share/icons/hicolor" 2>/dev/null || true

echo "installed $apps_dir/$wm_class.desktop"
echo "installed $icon_dir/$wm_class.svg"
echo "any tX/tfinal binary now reports app-id \"$wm_class\" and will show this icon in alt-tab/taskbar"
