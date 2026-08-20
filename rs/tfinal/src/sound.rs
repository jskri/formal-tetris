//! Procedural sound effects: synthesized at runtime, no audio asset files,
//! no music.
//!
//! R-SoundEngineLocal: one `SoundEngine` lives in `main()`'s own local state.
//! R-FailSoft: no audio output device degrades `play()` to a silent no-op.

use std::collections::HashMap;
use std::num::NonZero;
use std::sync::atomic::{AtomicBool, Ordering};

use rodio::mixer::Mixer;
use rodio::{DeviceSinkBuilder, MixerDeviceSink, Player};

const SAMPLE_RATE: u32 = 44_100;
/// Floor for exponential gain decay (true decay to 0 is undefined; ramp to
/// a small epsilon instead).
const MIN_GAIN: f32 = 0.001;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Waveform {
    Sine,
    Square,
    Triangle,
    Sawtooth,
}

/// One oscillator envelope: linear attack-free onset, exponential gain
/// decay to ~0 over `duration`; `slide_to`, when set, exponentially glides
/// `freq_hz` toward it over the same span.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct ToneSpec {
    pub waveform: Waveform,
    pub freq_hz: f32,
    pub duration: f32,
    pub gain: f32,
    pub slide_to: Option<f32>,
}

fn waveform_sample(w: Waveform, phase: f32) -> f32 {
    let x = phase - phase.floor(); // fractional part of the cycle, in [0, 1)
    match w {
        Waveform::Sine => (x * std::f32::consts::TAU).sin(),
        Waveform::Square => {
            if x < 0.5 {
                1.0
            } else {
                -1.0
            }
        }
        // asin(sin(..)) shaped: a true triangle wave, normalized to [-1, 1].
        Waveform::Triangle => {
            (std::f32::consts::FRAC_2_PI) * (x * std::f32::consts::TAU).sin().asin()
        }
        Waveform::Sawtooth => 2.0 * (x - (x + 0.5).floor()),
    }
}

/// Renders one `ToneSpec` to a mono sample buffer. Frequency and gain are
/// re-evaluated every sample rather than via a closed-form integral —
/// simpler, and accurate enough for sub-second sfx.
pub fn render_tone(spec: &ToneSpec, sample_rate: u32) -> Vec<f32> {
    let n = ((spec.duration.max(0.0)) * sample_rate as f32).round() as usize;
    let mut out = Vec::with_capacity(n);
    let mut phase = 0.0f32;
    let dt = 1.0 / sample_rate as f32;
    let gain_ratio = if spec.gain > 0.0 {
        MIN_GAIN / spec.gain
    } else {
        0.0
    };
    for i in 0..n {
        let t = i as f32 * dt;
        let frac = if spec.duration > 0.0 {
            (t / spec.duration).min(1.0)
        } else {
            1.0
        };
        let freq_now = match spec.slide_to {
            Some(target) if spec.freq_hz > 0.0 && target > 0.0 => {
                spec.freq_hz * (target / spec.freq_hz).powf(frac)
            }
            Some(target) => spec.freq_hz + (target - spec.freq_hz) * frac, // degenerate (zero-Hz) case: fall back to linear
            None => spec.freq_hz,
        };
        phase += freq_now * dt;
        let gain_now = if spec.gain > 0.0 {
            spec.gain * gain_ratio.powf(frac)
        } else {
            0.0
        };
        out.push(waveform_sample(spec.waveform, phase) * gain_now);
    }
    out
}

/// Each `(offset, spec)` pair renders independently and additively mixes
/// into one buffer starting at `offset` seconds — a sequenced arpeggio when
/// offsets are staggered, a simultaneous chord when they're all `0.0`.
pub fn render_chord(specs: &[(f32, ToneSpec)], sample_rate: u32) -> Vec<f32> {
    let mut total_len = 0usize;
    let mut rendered: Vec<(usize, Vec<f32>)> = Vec::with_capacity(specs.len());
    for (offset, spec) in specs {
        let start = (offset.max(0.0) * sample_rate as f32).round() as usize;
        let buf = render_tone(spec, sample_rate);
        total_len = total_len.max(start + buf.len());
        rendered.push((start, buf));
    }
    let mut out = vec![0.0f32; total_len];
    for (start, buf) in rendered {
        for (i, s) in buf.into_iter().enumerate() {
            out[start + i] += s;
        }
    }
    out
}

/// Every trigger this crate fires. `Clear`/`Combo`/`GarbageSlam` payloads
/// scale pitch and/or duration with the count; callers clamp them before
/// construction (`Clear` to `1..=4`, `Combo` to `0..=10`, `GarbageSlam` to
/// `0..=8`).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sfx {
    Move,
    Rotate,
    Hold,
    Fix,
    Drop,
    Clear(u8),
    PerfectClear,
    Combo(u8),
    LevelUp,
    Gameover,
    GarbageSlam(u8),
    Winner,
    Disconnect,
    HostLost,
}

enum Sound {
    Tone(ToneSpec),
    Chord(Vec<(f32, ToneSpec)>),
}

fn tone(
    waveform: Waveform,
    freq_hz: f32,
    duration: f32,
    gain: f32,
    slide_to: Option<f32>,
) -> ToneSpec {
    ToneSpec {
        waveform,
        freq_hz,
        duration,
        gain,
        slide_to,
    }
}

/// The fixed tone/chord definition for every `Sfx` value — a pure function
/// of the enum, never state.
fn sound_for(sfx: Sfx) -> Sound {
    use Waveform::*;
    match sfx {
        Sfx::Move => Sound::Tone(tone(Square, 220.0, 0.04, 0.10, None)),
        Sfx::Rotate => Sound::Tone(tone(Square, 330.0, 0.05, 0.10, None)),
        // Distinct from Fix: a deliberate action, not a piece running out of room.
        Sfx::Hold => Sound::Tone(tone(Triangle, 260.0, 0.06, 0.14, Some(400.0))),
        Sfx::Fix => Sound::Tone(tone(Triangle, 140.0, 0.08, 0.18, None)),
        // Hard drop: sharp downward "thwack" — fast pitch-drop, short.
        Sfx::Drop => Sound::Tone(tone(Square, 300.0, 0.06, 0.22, Some(60.0))),
        // Pitch/duration scale with lines cleared — a Tetris reads as bigger than a single.
        Sfx::Clear(n) => {
            let n = n as f32;
            Sound::Tone(tone(
                Sawtooth,
                500.0 + n * 60.0,
                0.12 + n * 0.05,
                0.18,
                Some(1400.0 + n * 100.0),
            ))
        }
        // Bright ascending chime, layered on top of Clear (not a replacement).
        Sfx::PerfectClear => Sound::Chord(vec![
            (0.00, tone(Sine, 900.0, 0.10, 0.16, None)),
            (0.09, tone(Sine, 1200.0, 0.10, 0.16, None)),
            (0.18, tone(Sine, 1600.0, 0.16, 0.18, None)),
        ]),
        // Rising blip, pitch scales with combo count.
        Sfx::Combo(n) => {
            let n = n as f32;
            Sound::Tone(tone(
                Square,
                500.0 + n * 40.0,
                0.07,
                0.14,
                Some(900.0 + n * 40.0),
            ))
        }
        // Brief rising sweep — a nod, not a fanfare, since it recurs every level-up.
        Sfx::LevelUp => Sound::Tone(tone(Triangle, 400.0, 0.14, 0.16, Some(700.0))),
        Sfx::Gameover => Sound::Tone(tone(Sawtooth, 200.0, 0.5, 0.15, Some(40.0))),
        // Garbage slam: short and brutal, not level-scaled — a hard downward hit.
        Sfx::GarbageSlam(n) => {
            let n = n as f32;
            Sound::Tone(tone(Sawtooth, 180.0, 0.08 + n * 0.01, 0.24, Some(40.0)))
        }
        // Winner fanfare: fuller than PerfectClear — the actual end-of-match payoff.
        Sfx::Winner => Sound::Chord(vec![
            (0.00, tone(Triangle, 700.0, 0.14, 0.18, None)),
            (0.12, tone(Triangle, 900.0, 0.14, 0.18, None)),
            (0.24, tone(Triangle, 1100.0, 0.14, 0.18, None)),
            (0.36, tone(Triangle, 1400.0, 0.30, 0.20, None)),
        ]),
        // Disconnect: deliberately unobtrusive — informational, not about this player's game.
        Sfx::Disconnect => Sound::Tone(tone(Sine, 300.0, 0.12, 0.10, Some(150.0))),
        // Host connection lost: the one alarm-like tone in the set.
        Sfx::HostLost => Sound::Chord(vec![
            (0.0, tone(Square, 500.0, 0.15, 0.20, None)),
            (0.2, tone(Square, 500.0, 0.15, 0.20, None)),
            (0.4, tone(Square, 500.0, 0.15, 0.20, None)),
        ]),
    }
}

fn render(sfx: Sfx, sample_rate: u32) -> Vec<f32> {
    match sound_for(sfx) {
        Sound::Tone(spec) => render_tone(&spec, sample_rate),
        Sound::Chord(specs) => render_chord(&specs, sample_rate),
    }
}

/// R-FixedCache: exhaustive list of every `Sfx` key (the clamp domain from
/// `Clear`/`Combo`/`GarbageSlam`).
fn all_sfx_keys() -> Vec<Sfx> {
    let mut v = vec![
        Sfx::Move,
        Sfx::Rotate,
        Sfx::Hold,
        Sfx::Fix,
        Sfx::Drop,
        Sfx::PerfectClear,
        Sfx::LevelUp,
        Sfx::Gameover,
        Sfx::Winner,
        Sfx::Disconnect,
        Sfx::HostLost,
    ];
    v.extend((1..=4).map(Sfx::Clear));
    v.extend((0..=10).map(Sfx::Combo));
    v.extend((0..=8).map(Sfx::GarbageSlam));
    v
}

/// Owns the audio output (if any), a precomputed sample cache, and the mute
/// flag. R-FixedCache: the cache is built once at construction.
pub struct SoundEngine {
    // Kept alive only so dropping it doesn't tear down the output stream
    // that every `Player` built from `mixer` needs; never read otherwise.
    _device_sink: Option<MixerDeviceSink>,
    mixer: Option<Mixer>,
    // R-ArcCache: caches built `SamplesBuffer`s so `play()` clones an Arc,
    // not the sample data.
    cache: HashMap<Sfx, rodio::buffer::SamplesBuffer>,
    muted: AtomicBool,
}

impl SoundEngine {
    pub fn new() -> Self {
        let (device_sink, mixer) = match DeviceSinkBuilder::open_default_sink() {
            Ok(mut sink) => {
                sink.log_on_drop(false);
                let mixer = sink.mixer().clone();
                (Some(sink), Some(mixer))
            }
            Err(e) => {
                eprintln!("sound: no audio output device ({e}); continuing muted");
                (None, None)
            }
        };
        let channels = NonZero::new(1u16).expect("1 is nonzero");
        let sample_rate = NonZero::new(SAMPLE_RATE).expect("SAMPLE_RATE is nonzero");
        let cache = all_sfx_keys()
            .into_iter()
            .map(|sfx| {
                (
                    sfx,
                    rodio::buffer::SamplesBuffer::new(
                        channels,
                        sample_rate,
                        render(sfx, SAMPLE_RATE),
                    ),
                )
            })
            .collect();
        SoundEngine {
            _device_sink: device_sink,
            mixer,
            cache,
            muted: AtomicBool::new(false),
        }
    }

    /// No-op while muted or with no audio device. R-DetachedPlayer: layers
    /// overlapping triggers instead of cutting each other off.
    pub fn play(&self, sfx: Sfx) {
        if self.muted.load(Ordering::Relaxed) {
            return;
        }
        let Some(mixer) = &self.mixer else { return };
        // Cache miss should be unreachable (call-site clamping), but never worth a panic.
        let Some(buf) = self.cache.get(&sfx) else {
            return;
        };
        let player = Player::connect_new(mixer);
        player.append(buf.clone()); // R-ArcCache: refcount bump, no sample copy
        player.detach();
    }

    pub fn toggle_muted(&self) -> bool {
        let was = self.muted.fetch_xor(true, Ordering::Relaxed);
        !was
    }

    pub fn is_muted(&self) -> bool {
        self.muted.load(Ordering::Relaxed)
    }
}

impl Default for SoundEngine {
    fn default() -> Self {
        Self::new()
    }
}
