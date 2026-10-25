//! Audio asset resolver.
//!
//! Compiles user-declared `sfx` and `music` blocks into the flat byte
//! tables consumed by the runtime audio driver, and provides builtin
//! fallback effects and tracks for unrecognized names (so legacy
//! programs that `play coin` / `start_music theme` without declaring
//! them still make sound).
//!
//! ## SFX representation
//!
//! Each [`SfxData`] is:
//!
//! - A few *compile-time constants* (`period_lo`, `period_hi`) that
//!   the IR codegen emits as immediates in the `play` instruction
//!   sequence to trigger a new pulse-1 note.
//! - A raw *envelope byte stream* stored in PRG ROM under the label
//!   `__sfx_<name>`, consumed one byte per NMI by the runtime audio
//!   tick. Each byte is a complete `$4000` write (duty<<6 | 0x30 |
//!   volume). A trailing zero byte is the sentinel: the tick sees
//!   it, mutes pulse 1, and stops.
//!
//! ## Music representation
//!
//! Each [`MusicData`] is:
//!
//! - A single compile-time `header` byte cached in ZP by
//!   `start_music` and used by the tick to build `$4004` envelope
//!   writes on every note change. Bit layout:
//!   - bit 0: loop flag
//!   - bits 2-5: volume (0-15)
//!   - bits 6-7: duty (0-3)
//! - A raw `(pitch, dur)` *note stream* stored in PRG ROM under the
//!   label `__music_<name>`, terminated by `(0xFF, 0xFF)`. Pitch 0 is
//!   a rest; pitches 1-60 are indices into the period table.

use crate::parser::ast::{Channel, MusicDecl, MusicNote, Program, SfxDecl};

/// Compiled sfx data.
///
/// Holds both the compile-time *trigger constants* written by the
/// `play` sequence (these depend on the destination channel) and
/// the per-frame *envelope blob* walked by the runtime audio tick
/// on every NMI. The envelope byte meaning also depends on the
/// channel:
///
/// - Pulse 1 / Pulse 2: each byte is a complete `$4000` / `$4004`
///   write (`DDlcvvvv` where `DD` = duty, `lc` = length-halt +
///   constant volume, `vvvv` = volume 0-15). A trailing `0x00` is
///   the mute sentinel.
/// - Noise: each byte is a complete `$400C` write using the exact
///   same `lcvvvv` encoding as pulse (the noise register has no
///   duty bits and ignores the top two). Trailing `0x00` is again
///   the mute sentinel.
/// - Triangle: triangle has no volume register, so each envelope
///   byte is instead a "linear counter reload" value for `$4008`.
///   The runtime writes it back on every tick so held notes don't
///   decay when the length counter underruns. The mute sentinel
///   (`0x80` — linear counter = 0 with the control bit set) tells
///   the runtime to silence the channel by writing `$80` to
///   `$4008` one last time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SfxData {
    pub name: String,
    /// Low byte of the trigger register written by `play`:
    /// - Pulse 1 / 2: `$4002` / `$4006` period low.
    /// - Triangle: `$400A` period low.
    /// - Noise: `$400E` period — low 4 bits select the period-table
    ///   index; we also stash a mode bit in bit 7 but default to 0
    ///   for tonal (non-metallic) noise.
    pub period_lo: u8,
    /// High byte of the trigger register written by `play`:
    /// - Pulse: `$4003` / `$4007` length-counter + period-high.
    /// - Triangle: `$400B` length-counter + period-high.
    /// - Noise: `$400F` length-counter load byte (pitch goes via
    ///   `$400E`, so this is just the length-counter reload).
    pub period_hi: u8,
    /// Per-frame envelope bytes walked by the audio tick one byte
    /// per NMI. Terminated by a channel-specific mute sentinel
    /// (`0x00` for pulse/noise, `0x80` for triangle). Linked into
    /// PRG ROM as a labelled data block.
    pub envelope: Vec<u8>,
    /// Per-frame pitch bytes. Empty when the sfx has a single
    /// scalar pitch (the existing latch-once behaviour) or when
    /// the channel doesn't currently support per-frame pitch
    /// updates (today only Pulse 1 does — triangle and noise
    /// share the same data shape but the runtime path hasn't been
    /// extended yet, see `docs/future-work.md`). When non-empty
    /// the audio tick writes one byte per NMI to the channel's
    /// period-lo register, in lockstep with the volume envelope.
    /// Length doesn't have to match `envelope` — the runtime
    /// re-reads the same byte each frame, so a shorter pitch
    /// stream simply latches its last value. The pitch stream
    /// has its own zero-byte sentinel matching the volume
    /// envelope's length so the lockstep walk terminates cleanly.
    pub pitch_envelope: Vec<u8>,
    /// APU channel this sfx drives.
    pub channel: Channel,
}

/// Compiled music data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MusicData {
    pub name: String,
    /// State byte cached by `start_music` into `ZP_MUSIC_STATE`. Bit
    /// 1 is OR'd in at runtime to mark the track active. Encodes
    /// duty (bits 6-7), volume (bits 2-5), and loop flag (bit 0).
    pub header: u8,
    /// Raw `(pitch, duration)` note stream terminated by
    /// `(0xFF, 0xFF)`. Linked into PRG ROM as a labelled data block.
    pub stream: Vec<u8>,
}

impl SfxData {
    /// ROM label for the in-PRG envelope blob. The IR codegen
    /// emits `LDA #<label` / `LDA #>label` pairs to load the
    /// pointer into `ZP_SFX_PTR_LO/HI` on `play`.
    #[must_use]
    pub fn label(&self) -> String {
        format!("__sfx_{}", sanitize_label(&self.name))
    }

    /// ROM label for the optional per-frame pitch envelope blob.
    /// Only meaningful when [`SfxData::pitch_envelope`] is
    /// non-empty; the codegen / linker uses it to splice the blob
    /// into PRG and to set up the pitch-walk pointer at trigger
    /// time. The label format mirrors the volume envelope label
    /// to keep `--symbols` output uniform.
    #[must_use]
    pub fn pitch_label(&self) -> String {
        format!("__sfx_pitch_{}", sanitize_label(&self.name))
    }

    /// True iff this sfx carries a per-frame pitch envelope. The
    /// runtime audio tick has a slightly different (and slightly
    /// larger) code path for sfx with pitch envelopes, so the
    /// codegen gates emission of that path on whether *any* sfx
    /// in the program has one.
    #[must_use]
    pub fn has_pitch_envelope(&self) -> bool {
        !self.pitch_envelope.is_empty()
    }
}

impl MusicData {
    /// ROM label for the in-PRG note-stream blob.
    #[must_use]
    pub fn label(&self) -> String {
        format!("__music_{}", sanitize_label(&self.name))
    }
}

/// Turn an audio asset name into a label-safe identifier. The
/// public API already restricts names to valid identifiers via the
/// parser, so this only has to protect against nonstandard input
/// from builtins (which currently use lowercase words).
fn sanitize_label(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Resolve a note name like `C4` / `Cs4` / `Db4` / `rest` into the
/// period-table index understood by the runtime music driver.
///
/// Returns:
/// - `Some(0)` for `rest` (silence)
/// - `Some(1..=60)` for a C1..B5 note
/// - `None` for anything else
///
/// The period table used by `runtime::gen_period_table` is laid out
/// one octave per 12 entries starting at C1 = index 1, so:
///
/// | Octave | First index | Last index |
/// |--------|-------------|------------|
/// | 1      | 1 (C1)      | 12 (B1)    |
/// | 2      | 13 (C2)     | 24 (B2)    |
/// | 3      | 25 (C3)     | 36 (B3)    |
/// | 4      | 37 (C4)     | 48 (B4)    |
/// | 5      | 49 (C5)     | 60 (B5)    |
///
/// Middle C is `C4` = 37.
///
/// Accidentals are written as `Cs4` (C sharp) or `Db4` (D flat); the
/// `#` and flat characters aren't valid `NEScript` identifiers, so
/// the two-letter prefix is the portable alternative. Names are
/// case-insensitive and equivalent enharmonic pairs
/// (e.g. `Cs4` / `Db4`) both resolve to the same index.
#[must_use]
pub fn note_name_to_index(name: &str) -> Option<u8> {
    let lower = name.to_ascii_lowercase();
    if lower == "rest" || lower == "_" {
        return Some(0);
    }
    // The shortest valid note name is 2 chars ("c1"), the longest is
    // 3 chars ("cs5"). Anything else can't be a note.
    let bytes = lower.as_bytes();
    if bytes.len() < 2 || bytes.len() > 3 {
        return None;
    }
    // Last char must be the octave digit.
    let octave = match bytes[bytes.len() - 1] {
        b'1' => 0u8,
        b'2' => 1,
        b'3' => 2,
        b'4' => 3,
        b'5' => 4,
        _ => return None,
    };
    // Step index within the octave: C=0, C#=1, D=2, D#=3, E=4,
    // F=5, F#=6, G=7, G#=8, A=9, A#=10, B=11.
    let step: u8 = match (bytes[0], bytes.get(1).copied()) {
        (b'c', Some(b's')) | (b'd', Some(b'b')) => 1,
        (b'c', _) => 0,
        (b'd', Some(b's')) | (b'e', Some(b'b')) => 3,
        (b'd', _) => 2,
        (b'e', _) => 4,
        (b'f', Some(b's')) | (b'g', Some(b'b')) => 6,
        (b'f', _) => 5,
        (b'g', Some(b's')) | (b'a', Some(b'b')) => 8,
        (b'g', _) => 7,
        (b'a', Some(b's')) | (b'b', Some(b'b')) => 10,
        (b'a', _) => 9,
        (b'b', _) => 11,
        _ => return None,
    };
    // If byte[1] is present it must have been consumed as an
    // accidental OR be the octave digit. Validate the accidental path
    // actually consumed byte[1].
    if bytes.len() == 3 {
        let acc = bytes[1];
        if acc != b's' && acc != b'b' {
            return None;
        }
    }
    Some(octave * 12 + step + 1)
}

/// Per-frame max (user-declared sfx length cap).
///
/// The driver walks envelope bytes one per NMI — a 60-frame sfx
/// lasts one second on NTSC. Anything much longer than that starts
/// overlapping with the next trigger and sounds muddy; cap at 120
/// (2 seconds) as a sanity check rather than a hard ROM constraint.
pub const SFX_MAX_FRAMES: usize = 120;

/// Per-track max notes (user-declared music length cap). The music
/// blob is 2 bytes per note plus a header and a 2-byte sentinel, so
/// 256 notes costs 515 ROM bytes — plenty for typical game loops.
pub const MUSIC_MAX_NOTES: usize = 256;

/// Resolve all user-declared `sfx` blocks in a program into compiled
/// byte blobs. Also appends builtin sfx data for any name referenced
/// in a `play` statement that isn't user-declared — this keeps legacy
/// programs working without explicit `sfx` declarations.
///
/// Returns an error if two user declarations share the same name, or
/// if any declaration exceeds the sfx length cap.
pub fn resolve_sfx(program: &Program) -> Result<Vec<SfxData>, String> {
    let mut out: Vec<SfxData> = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();

    // 1. User-declared sfx come first. Name collisions are an error.
    for decl in &program.sfx {
        if !seen.insert(decl.name.clone()) {
            return Err(format!("duplicate sfx declaration: '{}'", decl.name));
        }
        if decl.pitch.len() > SFX_MAX_FRAMES {
            return Err(format!(
                "sfx '{}' has {} frames, max is {}",
                decl.name,
                decl.pitch.len(),
                SFX_MAX_FRAMES
            ));
        }
        out.push(compile_sfx(decl));
    }

    // 2. Append builtin sfx for any referenced-but-undeclared names.
    // Walk every `play name` statement in the program and, for each
    // unfamiliar name that matches a builtin, synthesize a builtin
    // decl and compile it. We only emit each builtin once.
    let referenced = referenced_sfx_names(program);
    for name in &referenced {
        if seen.contains(name) {
            continue;
        }
        if let Some(decl) = builtin_sfx(name) {
            seen.insert(name.clone());
            out.push(compile_sfx(&decl));
        }
    }

    Ok(out)
}

/// Resolve all user-declared `music` blocks. Same shape as
/// [`resolve_sfx`] — user decls first, then builtins for any
/// referenced-but-undeclared names.
pub fn resolve_music(program: &Program) -> Result<Vec<MusicData>, String> {
    let mut out: Vec<MusicData> = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();

    for decl in &program.music {
        if !seen.insert(decl.name.clone()) {
            return Err(format!("duplicate music declaration: '{}'", decl.name));
        }
        if decl.notes.len() > MUSIC_MAX_NOTES {
            return Err(format!(
                "music '{}' has {} notes, max is {}",
                decl.name,
                decl.notes.len(),
                MUSIC_MAX_NOTES
            ));
        }
        out.push(compile_music(decl));
    }

    let referenced = referenced_music_names(program);
    for name in &referenced {
        if seen.contains(name) {
            continue;
        }
        if let Some(decl) = builtin_music(name) {
            seen.insert(name.clone());
            out.push(compile_music(&decl));
        }
    }

    Ok(out)
}

/// Compile one sfx declaration into its `SfxData`.
///
/// The compile-time constants (period) are derived from the *first*
/// pitch value in the array — v1 of the driver holds a fixed period
/// for the whole envelope so the channel doesn't retrigger mid-run.
/// Pitch variation across frames is ignored in this version.
///
/// The exact bytes emitted depend on the destination channel — see
/// [`SfxData`] for the per-channel format.
fn compile_sfx(decl: &SfxDecl) -> SfxData {
    match decl.channel {
        Channel::Pulse1 | Channel::Pulse2 => compile_pulse_sfx(decl),
        Channel::Triangle => compile_triangle_sfx(decl),
        Channel::Noise => compile_noise_sfx(decl),
    }
}

fn compile_pulse_sfx(decl: &SfxDecl) -> SfxData {
    let period_lo = decl.pitch.first().copied().unwrap_or(0);
    // length_hi: length counter load index 0 (254 frames), period hi = 0.
    // Bit 3 of $4003 = length counter enable; bits 0-2 = period high.
    let period_hi: u8 = 0x08;
    let mut envelope = Vec::with_capacity(decl.volume.len() + 1);
    for &vol in &decl.volume {
        let duty = decl.duty & 0x03;
        // $4000 format: DD LC VVVV. We always set L (length-halt)
        // and C (constant volume) so the envelope value is exactly
        // the user's volume number without APU envelope decay.
        let env = (duty << 6) | 0x30 | (vol & 0x0F);
        envelope.push(env);
    }
    // Zero sentinel — the audio tick sees this, mutes the channel,
    // and clears the sfx counter so subsequent NMIs don't keep walking.
    envelope.push(0x00);
    // Per-frame pitch envelope — populated when the user provides
    // more than one distinct pitch byte. A single scalar (or a
    // multi-element array where every byte is the same) keeps
    // the historical "latch period at trigger and never touch
    // it again" behaviour and emits no pitch blob, so existing
    // sfx ROMs are byte-identical. The pitch envelope is padded
    // (or truncated) to match the volume envelope length so the
    // runtime can walk both pointers in lockstep. The trailing
    // zero byte is *padding*, not a sentinel the runtime ever
    // reads — the volume tick `JMP`s to `__audio_sfx_done` on
    // its own zero sentinel before the pitch update block runs,
    // so the pitch pointer never advances past the user's last
    // byte. Keeping the trailing zero costs one ROM byte but
    // makes the blob length predictable for the linker symbol
    // dump and matches the `volume` envelope's shape.
    let pitch_envelope = build_pulse_pitch_envelope(&decl.pitch, decl.volume.len());
    SfxData {
        name: decl.name.clone(),
        period_lo,
        period_hi,
        envelope,
        pitch_envelope,
        channel: decl.channel,
    }
}

/// Build the pulse-channel pitch envelope from a user-declared
/// `pitch:` array. Returns an empty vector when the array
/// describes a single static pitch (length ≤ 1, or all bytes the
/// same), in which case the runtime keeps its existing latch-once
/// behaviour and no pitch blob is emitted at all. Otherwise the
/// returned vector has exactly `volume_frames + 1` bytes — the
/// extra byte is a zero sentinel that lines up with the volume
/// envelope's mute byte so the runtime tick sees both end markers
/// on the same NMI. Pitches shorter than `volume_frames` repeat
/// their last value; longer pitches truncate.
fn build_pulse_pitch_envelope(pitch: &[u8], volume_frames: usize) -> Vec<u8> {
    if pitch.len() <= 1 {
        return Vec::new();
    }
    if pitch.iter().all(|&p| p == pitch[0]) {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(volume_frames + 1);
    let last = *pitch.last().unwrap_or(&0);
    for i in 0..volume_frames {
        out.push(pitch.get(i).copied().unwrap_or(last));
    }
    out.push(0x00);
    out
}

/// Triangle envelope: each byte is a linear-counter reload value
/// written back to `$4008`. Nonzero means "continue holding the
/// note"; the sentinel `0x80` (linear counter = 0 with control bit
/// set to halt the length counter) tells the runtime to silence
/// the channel and stop walking the blob.
///
/// We map each user `volume` value to the linear-counter reload
/// value via `0x80 | 0x7F` = `0xFF` for the "hold" case — this
/// gives the maximum sustain count of 127 per frame, which the
/// runtime rewrites every tick anyway. Values of `0` in the user
/// array collapse to the mute sentinel immediately.
fn compile_triangle_sfx(decl: &SfxDecl) -> SfxData {
    // $400A = period low, $400B = length + period high.
    let period_lo = decl.pitch.first().copied().unwrap_or(0);
    // Bit 3 of $400B = length counter enable; we set it along with
    // period-high bits (always 0 at the user level).
    let period_hi: u8 = 0x08;
    let mut envelope = Vec::with_capacity(decl.volume.len() + 1);
    for &vol in &decl.volume {
        if vol == 0 {
            // Early release: user wrote a zero in the hold array.
            envelope.push(0x80);
        } else {
            // 0xFF = control bit set (halt length counter on 0) |
            // 0x7F reload value (~2.1 seconds of sustain). The
            // runtime rewrites this every tick so the channel
            // never underruns the linear counter.
            envelope.push(0xFF);
        }
    }
    // Sentinel: linear-counter control + 0 reload = silence.
    envelope.push(0x80);
    SfxData {
        name: decl.name.clone(),
        period_lo,
        period_hi,
        envelope,
        // Triangle per-frame pitch isn't wired up yet (the runtime
        // tick's triangle block writes only $4008, not $400A); see
        // docs/future-work.md for the gap.
        pitch_envelope: Vec::new(),
        channel: decl.channel,
    }
}

/// Noise envelope: each byte is a complete `$400C` write using the
/// same `lcvvvv` encoding as the pulse channels (duty bits are
/// unused by noise so we mask them out). The mute sentinel is
/// `0x00`, same as the pulse channels — it resolves to "constant
/// volume, volume = 0" which silences the channel.
///
/// The trigger byte (`period_lo`) is interpreted as a 4-bit index
/// into the APU's internal 16-entry noise period table (`$400E`
/// low nibble), plus an optional "mode" bit in position 7 that
/// switches between the long and short feedback-shift-register
/// patterns. We default to mode 0 (tonal).
fn compile_noise_sfx(decl: &SfxDecl) -> SfxData {
    // $400E = mode + period index. The user's `pitch` scalar is
    // the low-nibble index 0-15. Mask to be safe.
    let period_lo = decl.pitch.first().copied().unwrap_or(0) & 0x8F;
    // $400F length counter load: same bit layout as pulse/triangle,
    // load-index 1 = 254 frames. The length counter keeps the
    // channel gated until our envelope sentinel mutes it.
    let period_hi: u8 = 0x08;
    let mut envelope = Vec::with_capacity(decl.volume.len() + 1);
    for &vol in &decl.volume {
        // $400C format: ..LC VVVV (top two bits unused).
        // We set length-halt + constant-volume just like pulse.
        let env = 0x30 | (vol & 0x0F);
        envelope.push(env);
    }
    envelope.push(0x00);
    SfxData {
        name: decl.name.clone(),
        period_lo,
        period_hi,
        envelope,
        // Noise per-frame pitch (period-index sweeping) isn't
        // wired up yet — the existing runtime tick only updates
        // `$400C` per frame. See docs/future-work.md.
        pitch_envelope: Vec::new(),
        channel: decl.channel,
    }
}

/// Compile one music declaration into its `MusicData`.
fn compile_music(decl: &MusicDecl) -> MusicData {
    let duty = decl.duty & 0x03;
    let volume = decl.volume & 0x0F;
    let header = (duty << 6) | (volume << 2) | u8::from(decl.loops);
    let mut stream = Vec::with_capacity(decl.notes.len() * 2 + 2);
    for note in &decl.notes {
        stream.push(note.pitch);
        stream.push(note.duration);
    }
    // End-of-track sentinel. The driver loops or mutes based on the
    // state header's loop bit (ORed in by `start_music`).
    stream.push(0xFF);
    stream.push(0xFF);
    MusicData {
        name: decl.name.clone(),
        header,
        stream,
    }
}

/// Collect every sfx name referenced by a `play NAME` statement
/// anywhere in the program.
fn referenced_sfx_names(program: &Program) -> Vec<String> {
    let mut out = Vec::new();
    for state in &program.states {
        for block in state
            .on_enter
            .iter()
            .chain(state.on_exit.iter())
            .chain(state.on_frame.iter())
            .chain(state.on_scanline.iter().map(|(_, b)| b))
        {
            walk_for_play(block, &mut out);
        }
    }
    for func in &program.functions {
        walk_for_play(&func.body, &mut out);
    }
    out.sort();
    out.dedup();
    out
}

/// Collect every music name referenced by a `start_music NAME`
/// statement anywhere in the program.
fn referenced_music_names(program: &Program) -> Vec<String> {
    let mut out = Vec::new();
    for state in &program.states {
        for block in state
            .on_enter
            .iter()
            .chain(state.on_exit.iter())
            .chain(state.on_frame.iter())
            .chain(state.on_scanline.iter().map(|(_, b)| b))
        {
            walk_for_music(block, &mut out);
        }
    }
    for func in &program.functions {
        walk_for_music(&func.body, &mut out);
    }
    out.sort();
    out.dedup();
    out
}

fn walk_for_play(block: &crate::parser::ast::Block, out: &mut Vec<String>) {
    use crate::parser::ast::Statement;
    for stmt in &block.statements {
        match stmt {
            Statement::Play(name, _) => out.push(name.clone()),
            Statement::If(_, then_b, elifs, else_b, _) => {
                walk_for_play(then_b, out);
                for (_, b) in elifs {
                    walk_for_play(b, out);
                }
                if let Some(b) = else_b {
                    walk_for_play(b, out);
                }
            }
            Statement::While(_, b, _) => walk_for_play(b, out),
            Statement::Loop(b, _) => walk_for_play(b, out),
            Statement::For { body, .. } => walk_for_play(body, out),
            _ => {}
        }
    }
}

fn walk_for_music(block: &crate::parser::ast::Block, out: &mut Vec<String>) {
    use crate::parser::ast::Statement;
    for stmt in &block.statements {
        match stmt {
            Statement::StartMusic(name, _) => out.push(name.clone()),
            Statement::If(_, then_b, elifs, else_b, _) => {
                walk_for_music(then_b, out);
                for (_, b) in elifs {
                    walk_for_music(b, out);
                }
                if let Some(b) = else_b {
                    walk_for_music(b, out);
                }
            }
            Statement::While(_, b, _) => walk_for_music(b, out),
            Statement::Loop(b, _) => walk_for_music(b, out),
            Statement::For { body, .. } => walk_for_music(body, out),
            _ => {}
        }
    }
}

/// Return a builtin sfx declaration matching `name`, or `None` if the
/// name isn't a recognized builtin. Builtins cover the six classic
/// game-audio cliches: coin, jump, hit, click, cancel, shoot. Names
/// are matched case-insensitively with a few common aliases.
#[must_use]
pub fn builtin_sfx(name: &str) -> Option<SfxDecl> {
    use crate::lexer::Span;
    let lower = name.to_ascii_lowercase();
    let (duty, pitch_base, volume) = match lower.as_str() {
        // High, short, ascending blip — classic pickup chirp.
        "coin" | "pickup" | "collect" => (2u8, 0x50u8, vec![15, 14, 13, 11, 9, 7, 4, 2]),
        // Quick descending arc — jump ack.
        "jump" | "hop" => (2, 0x80, vec![13, 13, 12, 11, 9, 7, 5, 3]),
        // Low short blast — hit/damage/explode.
        "hit" | "damage" | "explode" => (1, 0xA0, vec![15, 14, 12, 10, 8, 6, 4, 2, 1]),
        // Sharp high beep — menu click/confirm.
        "click" | "select" | "confirm" => (2, 0x40, vec![12, 10, 6, 2]),
        // Low longer tone — cancel/back/error.
        "cancel" | "back" | "error" => (2, 0xB0, vec![14, 13, 12, 11, 10, 9, 8, 7, 6, 4]),
        // Very high, short — laser shoot.
        "shoot" | "laser" | "fire" => (3, 0x30, vec![15, 12, 9, 6, 3]),
        // Short low thud — footstep.
        "step" | "footstep" => (0, 0xC0, vec![10, 6, 2]),
        _ => return None,
    };
    // Pitch array is constant (one byte, since v1 format latches
    // the period once). Use pitch_base as the single entry.
    let frames = volume.len();
    Some(SfxDecl {
        name: name.to_string(),
        duty,
        pitch: vec![pitch_base; frames],
        volume,
        channel: Channel::Pulse1,
        span: Span::dummy(),
    })
}

/// Return a builtin music declaration matching `name`, or `None`.
/// Builtins are short single-channel loops played on pulse 2.
#[must_use]
pub fn builtin_music(name: &str) -> Option<MusicDecl> {
    use crate::lexer::Span;
    // Note indexes reference the period table in
    // `runtime::gen_period_table`: 1 = C1, 13 = C2, 25 = C3, 37 = C4.
    // Middle C = 37.
    const REST: u8 = 0;
    const C4: u8 = 37;
    const D4: u8 = 39;
    const E4: u8 = 41;
    const F4: u8 = 42;
    const G4: u8 = 44;
    const A4: u8 = 46;
    const B4: u8 = 48;
    const C5: u8 = 49;
    let lower = name.to_ascii_lowercase();
    let notes: Vec<MusicNote> = match lower.as_str() {
        // Cheerful major arpeggio — default theme.
        "title" | "theme" | "main" => [
            (C4, 12),
            (E4, 12),
            (G4, 12),
            (C5, 12),
            (G4, 12),
            (E4, 12),
            (C4, 12),
            (REST, 12),
        ]
        .iter()
        .map(|&(p, d)| MusicNote {
            pitch: p,
            duration: d,
        })
        .collect(),
        // Fast driving pulse — battle/boss.
        "battle" | "boss" => [
            (A4, 8),
            (C5, 8),
            (E4, 8),
            (A4, 8),
            (G4, 8),
            (B4, 8),
            (D4, 8),
            (G4, 8),
        ]
        .iter()
        .map(|&(p, d)| MusicNote {
            pitch: p,
            duration: d,
        })
        .collect(),
        // Fanfare — short ascending burst.
        "win" | "victory" | "fanfare" => [(C4, 10), (E4, 10), (G4, 10), (C5, 20), (REST, 10)]
            .iter()
            .map(|&(p, d)| MusicNote {
                pitch: p,
                duration: d,
            })
            .collect(),
        // Gloomy descending — game over.
        "gameover" | "lose" | "fail" => {
            [(C4, 20), (B4, 20), (A4, 20), (G4, 20), (F4, 30), (REST, 20)]
                .iter()
                .map(|&(p, d)| MusicNote {
                    pitch: p,
                    duration: d,
                })
                .collect()
        }
        _ => return None,
    };
    Some(MusicDecl {
        name: name.to_string(),
        duty: 2,
        volume: 10,
        loops: !matches!(lower.as_str(), "win" | "victory" | "fanfare"),
        notes,
        span: Span::dummy(),
    })
}

/// Return true if `name` matches a builtin sfx entry.
#[must_use]
pub fn is_builtin_sfx(name: &str) -> bool {
    builtin_sfx(name).is_some()
}

/// Return true if `name` matches a builtin music entry.
#[must_use]
pub fn is_builtin_music(name: &str) -> bool {
    builtin_music(name).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Span;
    use crate::parser::ast::*;

    fn empty_program() -> Program {
        Program {
            game: GameDecl {
                name: "T".to_string(),
                mapper: Mapper::NROM,
                mirroring: Mirroring::Horizontal,
                header: HeaderFormat::Ines1,
                debug_port: 0x4800,
                sprite_flicker: false,
                span: Span::dummy(),
            },
            globals: Vec::new(),
            saves: Vec::new(),
            constants: Vec::new(),
            enums: Vec::new(),
            structs: Vec::new(),
            functions: Vec::new(),
            states: Vec::new(),
            sprites: Vec::new(),
            palettes: Vec::new(),
            backgrounds: Vec::new(),
            metasprites: Vec::new(),
            metatilesets: Vec::new(),
            rooms: Vec::new(),
            sfx: Vec::new(),
            music: Vec::new(),
            banks: Vec::new(),
            start_state: "Main".to_string(),
            span: Span::dummy(),
        }
    }

    #[test]
    fn compile_sfx_splits_trigger_constants_from_envelope() {
        let decl = SfxDecl {
            name: "Test".to_string(),
            duty: 2,
            pitch: vec![0x50, 0x50, 0x50, 0x50],
            volume: vec![15, 10, 5, 0],
            channel: Channel::Pulse1,
            span: Span::dummy(),
        };
        let data = compile_sfx(&decl);
        // Compile-time constants land in fields, not bytes.
        assert_eq!(data.period_lo, 0x50);
        assert_eq!(data.period_hi, 0x08);
        // Envelope = 4 frames + sentinel.
        assert_eq!(data.envelope.len(), 5);
        // First envelope byte: duty 2 << 6 | 0x30 | 15 = 0xBF.
        assert_eq!(data.envelope[0], 0xBF);
        // Second: 0x80 | 0x30 | 10 = 0xBA.
        assert_eq!(data.envelope[1], 0xBA);
        // Last byte is the mute sentinel.
        assert_eq!(*data.envelope.last().unwrap(), 0x00);
    }

    #[test]
    fn compile_sfx_duty_0_clears_top_bits() {
        let decl = SfxDecl {
            name: "Soft".to_string(),
            duty: 0,
            pitch: vec![0x20],
            volume: vec![8],
            channel: Channel::Pulse1,
            span: Span::dummy(),
        };
        let data = compile_sfx(&decl);
        // env = 0 << 6 | 0x30 | 8 = 0x38
        assert_eq!(data.envelope[0], 0x38);
    }

    #[test]
    fn compile_sfx_noise_channel_strips_duty_and_pitches() {
        let decl = SfxDecl {
            name: "Zap".to_string(),
            duty: 3, // meaningless for noise; must not leak
            pitch: vec![0x05, 0x05, 0x05],
            volume: vec![15, 10, 5],
            channel: Channel::Noise,
            span: Span::dummy(),
        };
        let data = compile_sfx(&decl);
        assert_eq!(data.channel, Channel::Noise);
        // Trigger: period_lo = pitch & 0x8F.
        assert_eq!(data.period_lo, 0x05);
        // Envelope bytes: top two duty bits should be zero on noise.
        // 0x30 | 15 = 0x3F, 0x30 | 10 = 0x3A, 0x30 | 5 = 0x35, + sentinel.
        assert_eq!(data.envelope, vec![0x3F, 0x3A, 0x35, 0x00]);
    }

    #[test]
    fn compile_sfx_triangle_channel_uses_hold_sentinel() {
        let decl = SfxDecl {
            name: "Bass".to_string(),
            duty: 2,
            pitch: vec![60, 60],
            volume: vec![1, 0], // hold then release
            channel: Channel::Triangle,
            span: Span::dummy(),
        };
        let data = compile_sfx(&decl);
        assert_eq!(data.channel, Channel::Triangle);
        // Nonzero hold becomes 0xFF; zero release becomes 0x80.
        // Terminal mute sentinel is also 0x80.
        assert_eq!(data.envelope, vec![0xFF, 0x80, 0x80]);
    }

    #[test]
    fn sfx_data_channel_roundtrips_through_resolve() {
        let mut prog = empty_program();
        prog.sfx.push(SfxDecl {
            name: "Bang".to_string(),
            duty: 2,
            pitch: vec![3],
            volume: vec![15, 8],
            channel: Channel::Noise,
            span: Span::dummy(),
        });
        prog.sfx.push(SfxDecl {
            name: "Drone".to_string(),
            duty: 2,
            pitch: vec![60],
            volume: vec![1, 1, 1],
            channel: Channel::Triangle,
            span: Span::dummy(),
        });
        let resolved = resolve_sfx(&prog).unwrap();
        assert_eq!(resolved.len(), 2);
        // The channel field survives the resolve/compile passes.
        assert_eq!(resolved[0].channel, Channel::Noise);
        assert_eq!(resolved[1].channel, Channel::Triangle);
    }

    #[test]
    fn compile_music_header_encodes_loop_duty_volume() {
        let decl = MusicDecl {
            name: "Loop".to_string(),
            duty: 2,
            volume: 10,
            loops: true,
            notes: vec![MusicNote {
                pitch: 37,
                duration: 8,
            }],
            span: Span::dummy(),
        };
        let data = compile_music(&decl);
        // header = (2<<6) | (10<<2) | 1 = 0xA9
        let expected_header: u8 = (2 << 6) | (10 << 2) | 1;
        assert_eq!(data.header, expected_header);
        // Stream = (37, 8), (0xFF, 0xFF).
        assert_eq!(data.stream, vec![37, 8, 0xFF, 0xFF]);
    }

    #[test]
    fn compile_music_non_looping_clears_header_bit() {
        let decl = MusicDecl {
            name: "Once".to_string(),
            duty: 0,
            volume: 0,
            loops: false,
            notes: vec![MusicNote {
                pitch: 1,
                duration: 1,
            }],
            span: Span::dummy(),
        };
        let data = compile_music(&decl);
        assert_eq!(data.header & 0x01, 0, "loop bit must be clear");
    }

    #[test]
    fn sfx_label_is_deterministic_per_name() {
        let decl = SfxDecl {
            name: "Pickup".to_string(),
            duty: 2,
            pitch: vec![0x50],
            volume: vec![8],
            channel: Channel::Pulse1,
            span: Span::dummy(),
        };
        let data = compile_sfx(&decl);
        assert_eq!(data.label(), "__sfx_Pickup");
    }

    #[test]
    fn music_label_sanitizes_special_chars() {
        let data = MusicData {
            name: "Title Screen".to_string(),
            header: 0,
            stream: vec![0xFF, 0xFF],
        };
        assert_eq!(data.label(), "__music_Title_Screen");
    }

    #[test]
    fn resolve_sfx_includes_user_decls() {
        let mut prog = empty_program();
        prog.sfx.push(SfxDecl {
            name: "Zap".to_string(),
            duty: 2,
            pitch: vec![0x40, 0x40],
            volume: vec![15, 8],
            channel: Channel::Pulse1,
            span: Span::dummy(),
        });
        let resolved = resolve_sfx(&prog).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].name, "Zap");
        // No play statements, so no builtins pulled in.
        assert!(!resolved.iter().any(|s| s.name == "coin"));
    }

    #[test]
    fn resolve_sfx_appends_builtin_when_referenced() {
        let mut prog = empty_program();
        // Simulate `on frame { play coin }` as a direct AST build.
        prog.states.push(StateDecl {
            name: "Main".to_string(),
            locals: Vec::new(),
            on_enter: None,
            on_exit: None,
            on_frame: Some(Block {
                statements: vec![Statement::Play("coin".to_string(), Span::dummy())],
                span: Span::dummy(),
            }),
            on_scanline: Vec::new(),
            span: Span::dummy(),
        });
        let resolved = resolve_sfx(&prog).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].name, "coin");
    }

    #[test]
    fn resolve_sfx_user_decl_shadows_builtin() {
        // A user's `sfx coin { ... }` should take priority over the
        // builtin coin effect — otherwise `sfx coin` would be
        // confusing (users expect their definition to win).
        let mut prog = empty_program();
        prog.sfx.push(SfxDecl {
            name: "coin".to_string(),
            duty: 0,
            pitch: vec![0xAA],
            volume: vec![1],
            channel: Channel::Pulse1,
            span: Span::dummy(),
        });
        prog.states.push(StateDecl {
            name: "Main".to_string(),
            locals: Vec::new(),
            on_enter: None,
            on_exit: None,
            on_frame: Some(Block {
                statements: vec![Statement::Play("coin".to_string(), Span::dummy())],
                span: Span::dummy(),
            }),
            on_scanline: Vec::new(),
            span: Span::dummy(),
        });
        let resolved = resolve_sfx(&prog).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].period_lo, 0xAA, "user period should win");
    }

    #[test]
    fn resolve_sfx_rejects_duplicates() {
        let mut prog = empty_program();
        prog.sfx.push(SfxDecl {
            name: "Boom".to_string(),
            duty: 2,
            pitch: vec![0x40],
            volume: vec![8],
            channel: Channel::Pulse1,
            span: Span::dummy(),
        });
        prog.sfx.push(SfxDecl {
            name: "Boom".to_string(),
            duty: 2,
            pitch: vec![0x40],
            volume: vec![8],
            channel: Channel::Pulse1,
            span: Span::dummy(),
        });
        assert!(resolve_sfx(&prog).is_err());
    }

    #[test]
    fn resolve_sfx_rejects_oversize() {
        let mut prog = empty_program();
        prog.sfx.push(SfxDecl {
            name: "Long".to_string(),
            duty: 2,
            pitch: vec![0; SFX_MAX_FRAMES + 1],
            volume: vec![8; SFX_MAX_FRAMES + 1],
            channel: Channel::Pulse1,
            span: Span::dummy(),
        });
        assert!(resolve_sfx(&prog).is_err());
    }

    #[test]
    fn resolve_music_includes_user_decls() {
        let mut prog = empty_program();
        prog.music.push(MusicDecl {
            name: "Theme".to_string(),
            duty: 2,
            volume: 10,
            loops: true,
            notes: vec![MusicNote {
                pitch: 37,
                duration: 8,
            }],
            span: Span::dummy(),
        });
        let resolved = resolve_music(&prog).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].name, "Theme");
    }

    #[test]
    fn resolve_music_appends_builtin_when_referenced() {
        let mut prog = empty_program();
        prog.states.push(StateDecl {
            name: "Main".to_string(),
            locals: Vec::new(),
            on_enter: None,
            on_exit: None,
            on_frame: Some(Block {
                statements: vec![Statement::StartMusic("theme".to_string(), Span::dummy())],
                span: Span::dummy(),
            }),
            on_scanline: Vec::new(),
            span: Span::dummy(),
        });
        let resolved = resolve_music(&prog).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].name, "theme");
    }

    #[test]
    fn builtin_sfx_aliases_work() {
        assert!(builtin_sfx("coin").is_some());
        assert!(builtin_sfx("COIN").is_some());
        assert!(builtin_sfx("Pickup").is_some());
        assert!(builtin_sfx("unknown_nonsense").is_none());
    }

    #[test]
    fn builtin_music_aliases_work() {
        assert!(builtin_music("theme").is_some());
        assert!(builtin_music("BATTLE").is_some());
        assert!(builtin_music("Victory").is_some());
        assert!(builtin_music("not_a_track").is_none());
    }

    #[test]
    fn is_builtin_helpers_match_option_result() {
        for name in ["coin", "jump", "hit", "click", "cancel", "shoot", "step"] {
            assert!(is_builtin_sfx(name), "builtin sfx '{name}'");
        }
        for name in ["theme", "battle", "victory", "gameover"] {
            assert!(is_builtin_music(name), "builtin music '{name}'");
        }
        assert!(!is_builtin_sfx("totally_made_up"));
        assert!(!is_builtin_music("also_made_up"));
    }

    #[test]
    fn note_name_middle_c_is_index_37() {
        // The period-table's middle-C slot — every other note is
        // anchored relative to this, so regressions here silently
        // transpose every song in the program.
        assert_eq!(note_name_to_index("C4"), Some(37));
        assert_eq!(note_name_to_index("c4"), Some(37));
    }

    #[test]
    fn note_name_rest_maps_to_zero() {
        assert_eq!(note_name_to_index("rest"), Some(0));
        assert_eq!(note_name_to_index("REST"), Some(0));
        assert_eq!(note_name_to_index("_"), Some(0));
    }

    #[test]
    fn note_name_octave_range() {
        assert_eq!(note_name_to_index("C1"), Some(1));
        assert_eq!(note_name_to_index("B1"), Some(12));
        assert_eq!(note_name_to_index("C2"), Some(13));
        assert_eq!(note_name_to_index("C5"), Some(49));
        assert_eq!(note_name_to_index("B5"), Some(60));
    }

    #[test]
    fn note_name_enharmonic_equivalence() {
        // C# == Db, D# == Eb, etc. The music driver only has one slot
        // per pitch, so enharmonic spellings must collapse.
        assert_eq!(note_name_to_index("Cs4"), note_name_to_index("Db4"));
        assert_eq!(note_name_to_index("Ds4"), note_name_to_index("Eb4"));
        assert_eq!(note_name_to_index("Fs4"), note_name_to_index("Gb4"));
        assert_eq!(note_name_to_index("Gs4"), note_name_to_index("Ab4"));
        assert_eq!(note_name_to_index("As4"), note_name_to_index("Bb4"));
    }

    #[test]
    fn note_name_sharp_flat_indices() {
        // C# sits between C and D in the period table.
        let c4 = note_name_to_index("C4").unwrap();
        let cs4 = note_name_to_index("Cs4").unwrap();
        let d4 = note_name_to_index("D4").unwrap();
        assert_eq!(cs4, c4 + 1);
        assert_eq!(d4, c4 + 2);
    }

    #[test]
    fn note_name_invalid_names_return_none() {
        assert_eq!(note_name_to_index(""), None);
        assert_eq!(note_name_to_index("H4"), None); // H isn't a note
        assert_eq!(note_name_to_index("C0"), None); // below period table
        assert_eq!(note_name_to_index("C6"), None); // above period table
        assert_eq!(note_name_to_index("C#4"), None); // `#` not allowed in idents
        assert_eq!(note_name_to_index("Csx4"), None); // bogus accidental
        assert_eq!(note_name_to_index("CoolName"), None);
    }

    #[test]
    fn build_pulse_pitch_envelope_scalar_returns_empty() {
        // A single pitch byte (the historical scalar `pitch:` form)
        // keeps the latch-once driver path. The runtime never
        // reads the pitch envelope blob, and we don't want to
        // emit one — the empty vec signals that to the linker.
        assert!(build_pulse_pitch_envelope(&[0x40], 8).is_empty());
        // Same for "the user wrote an array but every element is
        // the same byte" — semantically identical to scalar pitch.
        assert!(build_pulse_pitch_envelope(&[0x40, 0x40, 0x40], 8).is_empty());
        // And the degenerate empty case.
        assert!(build_pulse_pitch_envelope(&[], 8).is_empty());
    }

    #[test]
    fn build_pulse_pitch_envelope_varying_pads_to_volume_length() {
        // The runtime walks pitch and volume in lockstep, so the
        // pitch blob is sized to match the volume envelope's
        // length plus a trailing zero sentinel.
        let env = build_pulse_pitch_envelope(&[0x40, 0x30, 0x20], 5);
        assert_eq!(
            env,
            vec![0x40, 0x30, 0x20, 0x20, 0x20, 0x00],
            "pitches shorter than volume frames should latch their last value"
        );
    }

    #[test]
    fn build_pulse_pitch_envelope_truncates_when_longer_than_volume() {
        // A pitch array longer than the volume envelope is
        // truncated — the runtime stops walking when the volume
        // envelope hits its zero sentinel anyway.
        let env = build_pulse_pitch_envelope(&[0x10, 0x20, 0x30, 0x40, 0x50, 0x60], 3);
        assert_eq!(env, vec![0x10, 0x20, 0x30, 0x00]);
    }

    #[test]
    fn compile_pulse_sfx_with_varying_pitch_populates_envelope() {
        // End-to-end: a pulse sfx with a varying `pitch:` array
        // should produce a non-empty `pitch_envelope` whose length
        // matches the volume envelope (excluding the sentinel),
        // and whose label is the canonical `__sfx_pitch_<name>`.
        let decl = SfxDecl {
            name: "Siren".to_string(),
            duty: 2,
            pitch: vec![0x40, 0x30, 0x20],
            volume: vec![15, 10, 5],
            channel: Channel::Pulse1,
            span: crate::lexer::Span::dummy(),
        };
        let sfx = compile_pulse_sfx(&decl);
        assert!(sfx.has_pitch_envelope());
        // Three volume frames + sentinel.
        assert_eq!(sfx.envelope.len(), 4);
        assert_eq!(sfx.pitch_envelope.len(), 4);
        assert_eq!(sfx.pitch_envelope[0], 0x40);
        assert_eq!(sfx.pitch_envelope[3], 0x00); // sentinel
        assert_eq!(sfx.pitch_label(), "__sfx_pitch_Siren");
    }

    #[test]
    fn compile_pulse_sfx_with_scalar_pitch_omits_envelope() {
        // The historical scalar form should still produce no
        // pitch envelope — gating the runtime extension on
        // emptiness keeps existing scalar-pitch ROMs byte-
        // identical.
        let decl = SfxDecl {
            name: "Coin".to_string(),
            duty: 2,
            pitch: vec![0x50],
            volume: vec![15, 10, 5],
            channel: Channel::Pulse1,
            span: crate::lexer::Span::dummy(),
        };
        let sfx = compile_pulse_sfx(&decl);
        assert!(!sfx.has_pitch_envelope());
        assert!(sfx.pitch_envelope.is_empty());
    }

    #[test]
    fn walk_for_play_finds_nested_references() {
        // `play` inside an `if` inside a `while` should still be
        // collected — the asset resolver needs to see every
        // referenced name so it can link in the right blob.
        let mut prog = empty_program();
        prog.states.push(StateDecl {
            name: "Main".to_string(),
            locals: Vec::new(),
            on_enter: None,
            on_exit: None,
            on_frame: Some(Block {
                statements: vec![Statement::While(
                    Expr::BoolLiteral(true, Span::dummy()),
                    Block {
                        statements: vec![Statement::If(
                            Expr::BoolLiteral(true, Span::dummy()),
                            Block {
                                statements: vec![Statement::Play(
                                    "jump".to_string(),
                                    Span::dummy(),
                                )],
                                span: Span::dummy(),
                            },
                            Vec::new(),
                            None,
                            Span::dummy(),
                        )],
                        span: Span::dummy(),
                    },
                    Span::dummy(),
                )],
                span: Span::dummy(),
            }),
            on_scanline: Vec::new(),
            span: Span::dummy(),
        });
        let names = referenced_sfx_names(&prog);
        assert_eq!(names, vec!["jump".to_string()]);
    }
}
