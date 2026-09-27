//! ESP32-U4WDH firmware.
//!
//! This chip is the Classic Bluetooth A2DP sink, the AVRCP controller, and
//! the only I2S master for the PCM5100A. The S3 sends transport commands,
//! tone requests, and companion OTA bytes over the UART. USB-C flashing
//! uses this chip's UART when the plug is flipped toward it.

use core::borrow::Borrow;

use std::sync::atomic::{AtomicBool, AtomicU16, AtomicU32, AtomicU8, Ordering};
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

use esp_idf_svc::bt::a2dp::{A2dpEvent, AudioStatus, ConnectionStatus, EspA2dp, Sink};
use esp_idf_svc::bt::avrc::controller::{AvrccEvent, EspAvrcc};
use esp_idf_svc::bt::avrc::{KeyCode, MetadataId, Notification, NotificationType, PlaybackStatus};
use esp_idf_svc::bt::gap::{
    Cod, CodMajorDeviceType, CodMode, CodServiceClass, DiscoveryMode, EspGap, GapEvent,
    IOCapabilities,
};
use esp_idf_svc::bt::{BdAddr, BtClassic, BtDriver};
use esp_idf_svc::hal::delay::{FreeRtos, NON_BLOCK};
use esp_idf_svc::hal::gpio::{AnyIOPin, PinDriver, Pull};
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::hal::uart::config::Config as UartConfig;
use esp_idf_svc::hal::uart::UartDriver;
use esp_idf_svc::hal::units::Hertz;
use esp_idf_svc::nvs::EspDefaultNvsPartition;
use esp_idf_svc::ota::{EspOta, EspOtaUpdate};
use esp_idf_svc::sys::{self, esp};

use enumset::EnumSet;

use knob::audio::{self, Tone};
use knob::ble::FIRMWARE_ID_ESP32;
use knob::board::{self, esp32 as pins, CLASSIC_BT_NAME};
use knob::encoder::Encoder;
use knob::link::{self, BtState, Decoder, MetaKind, Msg, PlayState};
use knob::ota::{self, OtaError, OtaSession, OtaTarget};

static PLAYING: AtomicBool = AtomicBool::new(false);
static TONE_HZ: AtomicU16 = AtomicU16::new(0);
static VOLUME: AtomicU16 = AtomicU16::new(160);
static CODEC_RATE: AtomicU32 = AtomicU32::new(0);
static TL: AtomicU8 = AtomicU8::new(1);
static PEER: Mutex<Option<[u8; 6]>> = Mutex::new(None);
static JACK: Mutex<Option<Jack>> = Mutex::new(None);
static NOTES: OnceLock<Mutex<Sender<Note>>> = OnceLock::new();

enum Note {
    Bt(BtState),
    Play(PlayState),
    Meta { kind: MetaKind, text: String },
    Device(String),
    Confirm([u8; 6]),
    Pin([u8; 6]),
    ArmAvrc,
    RefreshTrack,
}

fn main() -> anyhow::Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    log::info!("{FIRMWARE_ID_ESP32} starting");

    if let Err(err) = EspOta::new().and_then(|mut ota| ota.mark_running_slot_valid()) {
        log::warn!("mark slot valid: {err}");
    }

    let peripherals = Peripherals::take()?;
    let nvs = EspDefaultNvsPartition::take()?;

    set_unmuted(false);
    *JACK.lock().unwrap() = Some(Jack::open(audio::SAMPLE_RATE)?);
    set_unmuted(true);

    let mut link = UartDriver::new(
        peripherals.uart1,
        peripherals.pins.gpio23,
        peripherals.pins.gpio18,
        Option::<AnyIOPin>::None,
        Option::<AnyIOPin>::None,
        &UartConfig::new()
            .baudrate(Hertz(board::LINK_BAUD))
            .rx_fifo_size(2048)
            .tx_fifo_size(2048),
    )?;

    let mut encoder_a = PinDriver::input(peripherals.pins.gpio19)?;
    let mut encoder_b = PinDriver::input(peripherals.pins.gpio22)?;
    encoder_a.set_pull(Pull::Up)?;
    encoder_b.set_pull(Pull::Up)?;
    let mut encoder = Encoder::new();

    let (tx, rx) = mpsc::channel();
    let _ = NOTES.set(Mutex::new(tx));

    let driver = BtDriver::<BtClassic>::new(peripherals.modem, Some(nvs))?;
    let gap = EspGap::new(&driver)?;
    let avrc = EspAvrcc::new(&driver)?;
    let a2dp = EspA2dp::new_sink(&driver)?;
    subscribe_gap(&gap)?;
    subscribe_avrc(&avrc)?;
    subscribe_a2dp(&a2dp)?;
    gap.set_device_name(CLASSIC_BT_NAME)?;
    gap.set_ssp_io_cap(IOCapabilities::None)?;
    let _ = gap.set_pin("0000");
    let services = EnumSet::only(CodServiceClass::Audio) | CodServiceClass::Rendering;
    let _ = gap.set_cod(
        Cod::new(CodMajorDeviceType::AudioVideo, 6, services),
        CodMode::SetAll,
    );
    gap.set_scan_mode(true, DiscoveryMode::Discoverable)?;
    log::info!("classic bluetooth name {CLASSIC_BT_NAME}");

    send_msg(&mut link, &Msg::Jack { release: true });
    send_msg(&mut link, &Msg::BtState(BtState::Discoverable));
    send_msg(&mut link, &Msg::DeviceName(CLASSIC_BT_NAME.to_string()));

    let mut session = OtaSession::new();
    let mut flash: Option<EspOtaUpdate<'static>> = None;
    let mut decoder = Decoder::new();
    let mut tone = Tone::new(440.0);
    let mut tone_buf = [0i16; 512];
    let mut uart_buf = [0u8; 256];
    let boot = Instant::now();

    loop {
        drain_notes(&rx, &mut link, &gap, &avrc);
        for msg in read_link(&mut link, &mut uart_buf, &mut decoder) {
            on_link(msg, &mut link, &a2dp, &avrc, &gap, &mut session, &mut flash);
        }

        let now_ms = boot.elapsed().as_millis() as u64;
        let step = encoder.update(encoder_a.is_high(), encoder_b.is_high(), now_ms);
        if step != 0 {
            send_msg(&mut link, &Msg::Knob(step.clamp(-128, 127) as i8));
        }

        let streaming = PLAYING.load(Ordering::Relaxed);
        let hz = TONE_HZ.load(Ordering::Relaxed);
        if !streaming && hz > 0 {
            tone.hz = f32::from(hz);
            if let Ok(mut guard) = JACK.lock() {
                if let Some(jack) = guard.as_mut() {
                    let _ = jack.set_rate(audio::SAMPLE_RATE);
                    tone.fill(&mut tone_buf);
                    audio::apply_volume(&mut tone_buf, VOLUME.load(Ordering::Relaxed));
                    jack.write_i16(&tone_buf);
                }
            }
            FreeRtos::delay_ms(4);
        } else {
            FreeRtos::delay_ms(10);
        }
    }
}

fn subscribe_gap(gap: &EspGap<'_, BtClassic, &BtDriver<'_, BtClassic>>) -> anyhow::Result<()> {
    gap.subscribe(|event| match event {
        GapEvent::PairingUserConfirmationRequest { bd_addr, .. } => {
            post(Note::Confirm(bd_addr.addr()));
        }
        GapEvent::PairingPinRequest { bd_addr, .. } => post(Note::Pin(bd_addr.addr())),
        GapEvent::AuthenticationCompleted { device_name, .. } => {
            if !device_name.is_empty() {
                post(Note::Device(device_name.to_string()));
            }
        }
        GapEvent::RemoteName { name, .. } => {
            if !name.is_empty() {
                post(Note::Device(name.to_string()));
            }
        }
        _ => {}
    })?;
    Ok(())
}

fn subscribe_avrc(avrc: &EspAvrcc<'_, BtClassic, &BtDriver<'_, BtClassic>>) -> anyhow::Result<()> {
    avrc.subscribe(|event| match event {
        AvrccEvent::Metadata { id, text } => {
            if let Some(kind) = meta_kind(id) {
                post(Note::Meta {
                    kind,
                    text: text.to_string(),
                });
            }
        }
        AvrccEvent::Notification(Notification::Playback(status)) => {
            post(Note::Play(play_state(status)));
        }
        AvrccEvent::Notification(Notification::TrackChanged | Notification::NowPlaying) => {
            post(Note::RefreshTrack);
        }
        _ => {}
    })?;
    Ok(())
}

fn subscribe_a2dp(
    a2dp: &EspA2dp<'_, BtClassic, &BtDriver<'_, BtClassic>, Sink>,
) -> anyhow::Result<()> {
    a2dp.subscribe(|event| {
        match event {
            A2dpEvent::ConnectionState {
                bd_addr, status, ..
            } => on_a2dp_conn(bd_addr, status),
            A2dpEvent::AudioState { status, .. } => {
                let started = matches!(status, AudioStatus::Started);
                PLAYING.store(started, Ordering::Relaxed);
                post(Note::Play(if started {
                    PlayState::Playing
                } else {
                    PlayState::Paused
                }));
            }
            A2dpEvent::AudioCodecConfigured { codec, .. } => {
                if let Some(rate) = codec.bitrate() {
                    CODEC_RATE.store(rate, Ordering::Relaxed);
                }
            }
            A2dpEvent::SinkData(bytes) => write_stream(bytes),
            _ => {}
        }
        0
    })?;
    Ok(())
}

fn on_a2dp_conn(bd_addr: BdAddr, status: ConnectionStatus) {
    let state = match status {
        ConnectionStatus::Connected => {
            *PEER.lock().unwrap() = Some(bd_addr.addr());
            post(Note::ArmAvrc);
            BtState::Connected
        }
        ConnectionStatus::Connecting => BtState::Connecting,
        ConnectionStatus::Disconnected | ConnectionStatus::Disconnecting => {
            *PEER.lock().unwrap() = None;
            PLAYING.store(false, Ordering::Relaxed);
            BtState::Disconnected
        }
    };
    post(Note::Bt(state));
}

fn write_stream(bytes: &[u8]) {
    let rate = CODEC_RATE.load(Ordering::Relaxed);
    let volume = VOLUME.load(Ordering::Relaxed);
    let Ok(mut guard) = JACK.lock() else {
        return;
    };
    let Some(jack) = guard.as_mut() else {
        return;
    };
    if rate != 0 {
        let _ = jack.set_rate(rate);
    }
    let mut tmp = [0i16; 256];
    let mut off = 0;
    while off + 1 < bytes.len() {
        let n = ((bytes.len() - off) / 2).min(tmp.len());
        for (i, slot) in tmp.iter_mut().take(n).enumerate() {
            let at = off + i * 2;
            *slot = i16::from_le_bytes([bytes[at], bytes[at + 1]]);
        }
        audio::apply_volume(&mut tmp[..n], volume);
        jack.write_i16(&tmp[..n]);
        off += n * 2;
    }
}

fn drain_notes<'d, G, A>(
    rx: &Receiver<Note>,
    link: &mut UartDriver<'_>,
    gap: &EspGap<'d, BtClassic, G>,
    avrc: &EspAvrcc<'d, BtClassic, A>,
) where
    G: Borrow<BtDriver<'d, BtClassic>>,
    A: Borrow<BtDriver<'d, BtClassic>>,
{
    while let Ok(note) = rx.try_recv() {
        match note {
            Note::Bt(state) => send_msg(link, &Msg::BtState(state)),
            Note::Play(state) => {
                send_msg(link, &Msg::PlayState(state));
                let _ = avrc.register_notification(tl(), NotificationType::Playback, 0);
            }
            Note::Meta { kind, text } => send_msg(link, &Msg::Meta { kind, text }),
            Note::Device(name) => send_msg(link, &Msg::DeviceName(name)),
            Note::Confirm(addr) => {
                let _ = gap.reply_ssp_confirm(&BdAddr::from_bytes(addr), true);
            }
            Note::Pin(addr) => {
                let _ = gap.reply_variable_pin(&BdAddr::from_bytes(addr), Some(b"0000"));
            }
            Note::ArmAvrc => arm_avrc(avrc),
            Note::RefreshTrack => {
                request_meta(avrc);
                let _ = avrc.register_notification(tl(), NotificationType::TrackChanged, 0);
            }
        }
    }
}

fn on_link<'d, P, A, G>(
    msg: Msg,
    link: &mut UartDriver<'_>,
    a2dp: &EspA2dp<'d, BtClassic, P, Sink>,
    avrc: &EspAvrcc<'d, BtClassic, A>,
    gap: &EspGap<'d, BtClassic, G>,
    session: &mut OtaSession,
    flash: &mut Option<EspOtaUpdate<'static>>,
) where
    P: Borrow<BtDriver<'d, BtClassic>>,
    A: Borrow<BtDriver<'d, BtClassic>>,
    G: Borrow<BtDriver<'d, BtClassic>>,
{
    match msg {
        Msg::Ping => send_msg(link, &Msg::Pong),
        Msg::Play => tap(avrc, KeyCode::Play),
        Msg::Pause => tap(avrc, KeyCode::Pause),
        Msg::Next => tap(avrc, KeyCode::Forward),
        Msg::Prev => tap(avrc, KeyCode::Backward),
        Msg::VolUp => {
            bump_volume(16);
            tap(avrc, KeyCode::VolumeUp);
        }
        Msg::VolDown => {
            bump_volume(-16);
            tap(avrc, KeyCode::VolumeDown);
        }
        Msg::Pair => {
            let _ = gap.set_scan_mode(true, DiscoveryMode::Discoverable);
            send_msg(link, &Msg::BtState(BtState::Discoverable));
        }
        Msg::Disconnect => {
            if let Some(addr) = PEER.lock().unwrap().take() {
                let _ = a2dp.disconnect_sink(&BdAddr::from_bytes(addr));
            }
        }
        Msg::Reboot => {
            log::info!("reboot");
            unsafe { sys::esp_restart() }
        }
        Msg::Jack { release } => set_unmuted(release),
        Msg::Tone { hz } => TONE_HZ.store(hz, Ordering::Relaxed),
        Msg::OtaBegin { size, crc } => begin_ota(link, session, flash, size, crc),
        Msg::OtaChunk { seq, data } => push_ota(link, session, flash, seq, &data),
        Msg::OtaFinish => finish_ota(link, session, flash),
        Msg::OtaAbort => {
            abort_flash(flash);
            session.abort();
        }
        _ => {}
    }
}

fn begin_ota(
    link: &mut UartDriver<'_>,
    session: &mut OtaSession,
    flash: &mut Option<EspOtaUpdate<'static>>,
    size: u32,
    crc: u32,
) {
    abort_flash(flash);
    session.abort();
    if let Err(err) = session.begin(OtaTarget::Esp32, size, crc) {
        ack(link, 0, Some(err));
        return;
    }
    match start_flash() {
        Ok(update) => *flash = Some(update),
        Err(err) => {
            log::warn!("ota flash: {err}");
            session.note_error(OtaError::State);
            ack(link, 0, Some(OtaError::State));
        }
    }
}

fn push_ota(
    link: &mut UartDriver<'_>,
    session: &mut OtaSession,
    flash: &mut Option<EspOtaUpdate<'static>>,
    seq: u16,
    data: &[u8],
) {
    if let Err(err) = session.push(seq, data) {
        ack(link, seq, Some(err));
        return;
    }
    let Some(update) = flash.as_mut() else {
        session.note_error(OtaError::State);
        ack(link, seq, Some(OtaError::State));
        return;
    };
    if let Err(err) = update.write(data) {
        log::warn!("ota write: {err}");
        session.note_error(OtaError::State);
        ack(link, seq, Some(OtaError::State));
        return;
    }
    ack(link, seq, None);
}

fn finish_ota(
    link: &mut UartDriver<'_>,
    session: &mut OtaSession,
    flash: &mut Option<EspOtaUpdate<'static>>,
) {
    if let Err(err) = session.finish() {
        abort_flash(flash);
        ack(link, 0, Some(err));
        return;
    }
    let Some(update) = flash.take() else {
        ack(link, 0, Some(OtaError::State));
        return;
    };
    if let Err(err) = update.complete() {
        log::warn!("ota complete: {err}");
        ack(link, 0, Some(OtaError::State));
        return;
    }
    ack(link, 0, None);
}

fn ack(link: &mut UartDriver<'_>, seq: u16, err: Option<OtaError>) {
    send_msg(
        link,
        &Msg::OtaAck {
            seq,
            err: err.map(ota::error_code).unwrap_or(0),
        },
    );
}

fn start_flash() -> Result<EspOtaUpdate<'static>, sys::EspError> {
    let ota: &'static mut EspOta = Box::leak(Box::new(EspOta::new()?));
    ota.initiate_update()
}

fn abort_flash(flash: &mut Option<EspOtaUpdate<'static>>) {
    if let Some(update) = flash.take() {
        let _ = update.abort();
    }
}

fn arm_avrc<T>(avrc: &EspAvrcc<'_, BtClassic, T>)
where
    T: Borrow<BtDriver<'_, BtClassic>>,
{
    request_meta(avrc);
    let _ = avrc.register_notification(tl(), NotificationType::Playback, 0);
    let _ = avrc.register_notification(tl(), NotificationType::TrackChanged, 0);
}

fn request_meta<T>(avrc: &EspAvrcc<'_, BtClassic, T>)
where
    T: Borrow<BtDriver<'_, BtClassic>>,
{
    let mut meta = EnumSet::empty();
    meta.insert(MetadataId::Title);
    meta.insert(MetadataId::Artist);
    meta.insert(MetadataId::Album);
    let _ = avrc.request_metadata(tl(), meta);
}

fn tap<T>(avrc: &EspAvrcc<'_, BtClassic, T>, key: KeyCode)
where
    T: Borrow<BtDriver<'_, BtClassic>>,
{
    let _ = avrc.send_passthrough(tl(), key, true);
    FreeRtos::delay_ms(30);
    let _ = avrc.send_passthrough(tl(), key, false);
}

fn tl() -> u8 {
    TL.fetch_add(1, Ordering::Relaxed) & 0x0F
}

fn bump_volume(delta: i16) {
    let cur = VOLUME.load(Ordering::Relaxed) as i16;
    VOLUME.store((cur + delta).clamp(0, 256) as u16, Ordering::Relaxed);
}

fn post(note: Note) {
    let Some(slot) = NOTES.get() else {
        return;
    };
    if let Ok(tx) = slot.lock() {
        let _ = tx.send(note);
    }
}

fn meta_kind(id: MetadataId) -> Option<MetaKind> {
    match id {
        MetadataId::Title => Some(MetaKind::Title),
        MetadataId::Artist => Some(MetaKind::Artist),
        MetadataId::Album => Some(MetaKind::Album),
        _ => None,
    }
}

fn play_state(status: PlaybackStatus) -> PlayState {
    match status {
        PlaybackStatus::Playing => PlayState::Playing,
        PlaybackStatus::Paused => PlayState::Paused,
        PlaybackStatus::Stopped => PlayState::Stopped,
        _ => PlayState::Unknown,
    }
}

fn read_link(uart: &mut UartDriver<'_>, buf: &mut [u8], decoder: &mut Decoder) -> Vec<Msg> {
    let mut out = Vec::new();
    loop {
        let n = match uart.read(buf, NON_BLOCK) {
            Ok(0) | Err(_) => break,
            Ok(n) => n,
        };
        for item in decoder.push(&buf[..n]) {
            if let Ok(msg) = item {
                out.push(msg);
            }
        }
        if n < buf.len() {
            break;
        }
    }
    out
}

fn send_msg(uart: &mut UartDriver<'_>, msg: &Msg) {
    let Ok(frame) = link::encode(msg) else {
        return;
    };
    let mut off = 0;
    while off < frame.len() {
        match uart.write(&frame[off..]) {
            Ok(0) | Err(_) => break,
            Ok(n) => off += n,
        }
    }
}

/// PCM5100A `XSMT` is active high. `unmuted` drives the pin high.
fn set_unmuted(unmuted: bool) {
    unsafe {
        let cfg = sys::gpio_config_t {
            pin_bit_mask: 1u64 << (pins::DAC_UNMUTE as u32),
            mode: sys::gpio_mode_t_GPIO_MODE_OUTPUT,
            pull_up_en: sys::gpio_pullup_t_GPIO_PULLUP_DISABLE,
            pull_down_en: sys::gpio_pulldown_t_GPIO_PULLDOWN_DISABLE,
            intr_type: sys::gpio_int_type_t_GPIO_INTR_DISABLE,
        };
        let _ = sys::gpio_config(&cfg);
        let _ = sys::gpio_set_level(pins::DAC_UNMUTE, i32::from(unmuted));
    }
}

/// Philips I2S master into the PCM5100A. 16-bit stereo.
///
/// The companion is a classic ESP32 (`SOC_I2S_HW_VERSION_1`), so the slot
/// config carries `msb_right`. The channel handle is a raw pointer. `JACK`
/// is the only way to reach it, and every use holds that mutex.
struct Jack {
    tx: sys::i2s_chan_handle_t,
    rate: u32,
}

unsafe impl Send for Jack {}

impl Jack {
    fn open(rate: u32) -> Result<Self, sys::EspError> {
        unsafe {
            let mut tx: sys::i2s_chan_handle_t = core::ptr::null_mut();
            let chan = sys::i2s_chan_config_t {
                id: sys::i2s_port_t_I2S_NUM_0,
                role: sys::i2s_role_t_I2S_ROLE_MASTER,
                dma_desc_num: 6,
                dma_frame_num: 240,
                auto_clear: true,
                intr_priority: 0,
            };
            esp!(sys::i2s_new_channel(&chan, &mut tx, core::ptr::null_mut()))?;
            let std = sys::i2s_std_config_t {
                clk_cfg: sys::i2s_std_clk_config_t {
                    sample_rate_hz: rate,
                    clk_src: sys::soc_periph_i2s_clk_src_t_I2S_CLK_SRC_DEFAULT,
                    mclk_multiple: sys::i2s_mclk_multiple_t_I2S_MCLK_MULTIPLE_256,
                },
                slot_cfg: sys::i2s_std_slot_config_t {
                    data_bit_width: 16,
                    slot_bit_width: 0,
                    slot_mode: sys::i2s_slot_mode_t_I2S_SLOT_MODE_STEREO,
                    slot_mask: sys::i2s_std_slot_mask_t_I2S_STD_SLOT_BOTH,
                    ws_width: 16,
                    ws_pol: false,
                    bit_shift: true,
                    msb_right: true,
                },
                gpio_cfg: sys::i2s_std_gpio_config_t {
                    mclk: sys::gpio_num_t_GPIO_NUM_NC,
                    bclk: pins::I2S_BCLK,
                    ws: pins::I2S_WS,
                    dout: pins::I2S_DOUT,
                    din: sys::gpio_num_t_GPIO_NUM_NC,
                    invert_flags: core::mem::zeroed(),
                },
            };
            if let Err(err) = esp!(sys::i2s_channel_init_std_mode(tx, &std)) {
                sys::i2s_del_channel(tx);
                return Err(err);
            }
            if let Err(err) = esp!(sys::i2s_channel_enable(tx)) {
                sys::i2s_del_channel(tx);
                return Err(err);
            }
            Ok(Self { tx, rate })
        }
    }

    fn set_rate(&mut self, rate: u32) -> Result<(), sys::EspError> {
        if self.rate == rate || rate == 0 {
            return Ok(());
        }
        log::info!("i2s {} -> {rate}", self.rate);
        let previous = self.rate;
        unsafe {
            sys::i2s_channel_disable(self.tx);
            sys::i2s_del_channel(self.tx);
        }
        self.tx = core::ptr::null_mut();
        match Self::open(rate) {
            Ok(next) => {
                *self = next;
                Ok(())
            }
            Err(err) => {
                if let Ok(fallback) = Self::open(previous) {
                    *self = fallback;
                }
                Err(err)
            }
        }
    }

    fn write_i16(&mut self, samples: &[i16]) {
        if self.tx.is_null() || samples.is_empty() {
            return;
        }
        let bytes = unsafe {
            core::slice::from_raw_parts(samples.as_ptr().cast::<u8>(), samples.len() * 2)
        };
        let mut wrote = 0usize;
        let _ = unsafe {
            sys::i2s_channel_write(
                self.tx,
                bytes.as_ptr().cast::<core::ffi::c_void>(),
                bytes.len(),
                &mut wrote,
                20,
            )
        };
    }
}
