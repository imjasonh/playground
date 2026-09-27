//! ESP32-S3 firmware.
//!
//! The round panel, encoder, touch, haptics, microphone, battery, card,
//! BLE, and the UART link to the companion all live on this chip. The
//! 3.5 mm jack is the companion's I2S DAC. GPIO0 stays low so the CH445P
//! keeps that path selected. USB-C flashing uses the S3's USB Serial/JTAG when the
//! plug is flipped toward this MCU. A later iOS app pushes a new image
//! over the GATT service in `knob::ble`.

use std::sync::mpsc::{self, Sender};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

use esp_idf_svc::eventloop::EspSystemEventLoop;
use esp_idf_svc::fs::fatfs::Fatfs;
use esp_idf_svc::hal::adc::attenuation::DB_12;
use esp_idf_svc::hal::adc::oneshot::config::{AdcChannelConfig, Calibration};
use esp_idf_svc::hal::adc::oneshot::{AdcChannelDriver, AdcDriver};
use esp_idf_svc::hal::adc::Resolution;
use esp_idf_svc::hal::delay::{FreeRtos, BLOCK, NON_BLOCK};
use esp_idf_svc::hal::gpio::{AnyIOPin, PinDriver, Pull};
use esp_idf_svc::hal::i2c::{I2cConfig, I2cDriver};
use esp_idf_svc::hal::i2s::config::{
    Config as I2sClock, DataBitWidth, PdmRxClkConfig, PdmRxConfig, PdmRxGpioConfig,
    PdmRxSlotConfig, SlotMode,
};
use esp_idf_svc::hal::i2s::{I2sDriver, I2sRx};
use esp_idf_svc::hal::ledc::config::TimerConfig;
use esp_idf_svc::hal::ledc::{LedcDriver, LedcTimerDriver, Resolution as LedcBits};
use esp_idf_svc::hal::modem::Modem;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::hal::sd::mmc::{SdMmcHostConfiguration, SdMmcHostDriver};
use esp_idf_svc::hal::sd::{SdCardConfiguration, SdCardDriver};
use esp_idf_svc::hal::spi::config::{Config as SpiConfig, DriverConfig, Duplex, LineWidth};
use esp_idf_svc::hal::spi::{Dma, Operation, SpiDeviceDriver, SpiDriver};
use esp_idf_svc::hal::uart::config::Config as UartConfig;
use esp_idf_svc::hal::uart::UartDriver;
use esp_idf_svc::hal::units::{FromValueType, Hertz};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs};
use esp_idf_svc::ota::{EspOta, EspOtaUpdate};
use esp_idf_svc::sys;
use esp_idf_svc::wifi::{
    AuthMethod, BlockingWifi, ClientConfiguration, Configuration as WifiConfig, EspWifi,
};

use esp32_nimble::utilities::BleUuid;
use esp32_nimble::{uuid128, BLEAdvertisementData, BLECharacteristic, BLEDevice, NimbleProperties};

use knob::apps::{self, SdEntry, World};
use knob::battery::{millivolts, percent};
use knob::ble::{self, TextCmd, DEVICE_NAME, FIRMWARE_ID_S3};
use knob::board::{self, PANEL_W};
use knob::canvas::Canvas;
use knob::encoder::Encoder;
use knob::haptic::{self, STRONG_CLICK};
use knob::hid;
use knob::link::{self, BtState, Decoder, Msg, PlayState};
use knob::mic;
use knob::ota::{self, opcode, OtaSession, OtaTarget};
use knob::shell::Shell;
use knob::st77916::{self, CASET, RAMWR, RASET};
use knob::touch::{self, TouchReport};

const I2C_HZ: u32 = 400_000;
const MIC_RATE: u32 = 16_000;
const LINK_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(3);

/// Events posted from the NimBLE task. Flash and UART stay on the main task.
enum Phone {
    Text(String),
    OtaControl(Vec<u8>),
    OtaData { seq: u16, bytes: Vec<u8> },
}

static PHONE: OnceLock<Mutex<Sender<Phone>>> = OnceLock::new();

fn main() -> anyhow::Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    log::info!("{FIRMWARE_ID_S3} starting");

    if let Err(err) = EspOta::new().and_then(|mut ota| ota.mark_running_slot_valid()) {
        log::warn!("mark slot valid: {err}");
    }

    let peripherals = Peripherals::take()?;
    let nvs = EspDefaultNvsPartition::take()?;
    let sysloop = EspSystemEventLoop::take()?;

    let timer = LedcTimerDriver::new(
        peripherals.ledc.timer0,
        &TimerConfig::default()
            .frequency(25_u32.kHz().into())
            .resolution(LedcBits::Bits10),
    )?;
    let mut backlight =
        LedcDriver::new(peripherals.ledc.channel0, &timer, peripherals.pins.gpio47)?;
    backlight.set_duty(backlight.get_max_duty())?;

    let mut lcd_reset = PinDriver::output(peripherals.pins.gpio21)?;
    lcd_reset.set_low()?;
    FreeRtos::delay_ms(20);
    lcd_reset.set_high()?;
    FreeRtos::delay_ms(120);
    let spi = SpiDriver::new_quad(
        peripherals.spi2,
        peripherals.pins.gpio13,
        peripherals.pins.gpio15,
        peripherals.pins.gpio16,
        peripherals.pins.gpio17,
        peripherals.pins.gpio18,
        &DriverConfig::new().dma(Dma::Auto(8192)),
    )?;
    let spi_config = SpiConfig::new()
        .baudrate(40_u32.MHz().into())
        .duplex(Duplex::Half)
        .write_only(true)
        .polling(true);
    let mut panel = SpiDeviceDriver::new(spi, Some(peripherals.pins.gpio14), &spi_config)?;
    init_panel(&mut panel)?;

    let mut i2c = I2cDriver::new(
        peripherals.i2c0,
        peripherals.pins.gpio11,
        peripherals.pins.gpio12,
        &I2cConfig::new().baudrate(Hertz(I2C_HZ)),
    )?;
    let mut touch_reset = PinDriver::output(peripherals.pins.gpio10)?;
    touch_reset.set_low()?;
    FreeRtos::delay_ms(10);
    touch_reset.set_high()?;
    FreeRtos::delay_ms(50);
    let touch_irq = PinDriver::input(peripherals.pins.gpio9, Pull::Up)?;
    // DRV2605 EN is tied to 3.3V on the schematic. GPIO38 is the UART TX.
    for write in haptic::boot() {
        let _ = i2c.write(haptic::ADDR, &[write.reg, write.val], BLOCK);
    }

    let encoder_a = PinDriver::input(peripherals.pins.gpio8, Pull::Up)?;
    let encoder_b = PinDriver::input(peripherals.pins.gpio7, Pull::Up)?;

    let mut dac_switch = PinDriver::output(peripherals.pins.gpio0)?;
    dac_switch.set_low()?;

    let mut mic_in = I2sDriver::<I2sRx>::new_pdm_rx(
        peripherals.i2s1,
        &PdmRxConfig::new(
            I2sClock::default(),
            PdmRxClkConfig::from_sample_rate_hz(MIC_RATE),
            PdmRxSlotConfig::from_bits_per_sample_and_slot_mode(
                DataBitWidth::Bits16,
                SlotMode::Mono,
            ),
            PdmRxGpioConfig::default(),
        ),
        peripherals.pins.gpio45,
        peripherals.pins.gpio46,
    )?;
    mic_in.rx_enable()?;

    let adc = AdcDriver::new(peripherals.adc1)?;
    let mut battery_pin = AdcChannelDriver::new(
        &adc,
        peripherals.pins.gpio1,
        &AdcChannelConfig {
            attenuation: DB_12,
            resolution: Resolution::Resolution12Bit,
            calibration: Calibration::None,
        },
    )?;

    let sd_host = SdMmcHostDriver::new_4bits(
        peripherals.sdmmc1,
        peripherals.pins.gpio3,
        peripherals.pins.gpio4,
        peripherals.pins.gpio5,
        peripherals.pins.gpio6,
        peripherals.pins.gpio42,
        peripherals.pins.gpio2,
        None::<AnyIOPin>,
        None::<AnyIOPin>,
        &SdMmcHostConfiguration::new(),
    );
    let mut sd_fs = match sd_host {
        Ok(host) => match SdCardDriver::new_mmc(host, &SdCardConfiguration::new()) {
            Ok(card) => Fatfs::new_sdcard(0, card).ok(),
            Err(err) => {
                log::warn!("sd card: {err}");
                None
            }
        },
        Err(err) => {
            log::warn!("sd host: {err}");
            None
        }
    };
    let _sd_mount = sd_fs.as_mut().and_then(|fs| match fs.mount() {
        Ok(mounted) => Some(mounted),
        Err(err) => {
            log::warn!("sd mount: {err}");
            None
        }
    });

    let mut link = UartDriver::new(
        peripherals.uart1,
        peripherals.pins.gpio38,
        peripherals.pins.gpio48,
        Option::<AnyIOPin>::None,
        Option::<AnyIOPin>::None,
        &UartConfig::new()
            .baudrate(Hertz(board::LINK_BAUD))
            .rx_fifo_size(2048)
            .tx_fifo_size(2048),
    )?;

    let (phone_tx, phone_rx) = mpsc::channel();
    let _ = PHONE.set(Mutex::new(phone_tx));
    let gatt = start_radio()?;

    let mut modem: Option<Modem<'static>> = Some(peripherals.modem);
    let mut wifi: Option<BlockingWifi<EspWifi<'static>>> = None;
    let mut pending_wifi = load_wifi(&nvs);
    let mut sntp_on = false;

    let mut shell = Shell::new(Canvas::panel());
    let mut encoder = Encoder::new();
    let mut session = OtaSession::new();
    let mut flash: Option<EspOtaUpdate<'static>> = None;
    let mut decoder = Decoder::new();
    let mut tone_hz: Option<u16> = None;
    let mut sent_tone: Option<u16> = None;
    let mut mic_pcm = [0i16; 512];
    let mut mic_at = 0usize;
    let mut mic_scratch = [0u8; 512];
    let mut bands = [0u8; mic::BANDS];
    let mut sd_entries: Vec<SdEntry> = Vec::new();
    let mut battery_mv: u32 = 0;
    let mut battery_pct: u8 = 0;
    let mut bt = BtState::Disconnected;
    let mut play = PlayState::Unknown;
    let mut track = String::new();
    let mut link_up = false;
    let mut last_link = Instant::now();
    let mut last_ping = Instant::now() - std::time::Duration::from_secs(3);
    let mut last_sd = Instant::now() - std::time::Duration::from_secs(3);
    let mut last_status = Instant::now();
    let mut last_battery = Instant::now();
    let mut release_hid = false;
    let mut rx = [0u8; 256];
    let mut remote_knob = 0i32;
    let mut pending_detent = 0i32;
    let mut link_msgs = Vec::new();
    let mut decoded = Vec::new();
    let mut strip = vec![0u8; usize::from(PANEL_W) * 4 * 2];
    let mut last_frame = Instant::now() - std::time::Duration::from_millis(20);
    let boot = Instant::now();

    loop {
        if last_ping.elapsed() >= std::time::Duration::from_secs(2) {
            send_msg(&mut link, &Msg::Ping);
            last_ping = Instant::now();
        }
        read_link(
            &mut link,
            &mut rx,
            &mut decoder,
            &mut link_msgs,
            &mut decoded,
        );
        for msg in link_msgs.drain(..) {
            last_link = Instant::now();
            link_up = true;
            match msg {
                Msg::Pong => {}
                Msg::BtState(state) => bt = state,
                Msg::PlayState(state) => play = state,
                Msg::Meta { text, .. } => track = text,
                Msg::DeviceName(name) => {
                    if track.is_empty() {
                        track = name;
                    }
                }
                Msg::Jack { release } => {
                    send_msg(&mut link, &Msg::Jack { release });
                }
                Msg::OtaAck { err, .. } => {
                    if err != 0 {
                        session.note_error(ota::OtaError::State);
                        log::warn!("companion ota ack {err}");
                    }
                }
                Msg::Knob(delta) => {
                    remote_knob = remote_knob.saturating_add(i32::from(delta));
                }
                other => log::info!("link {other:?}"),
            }
        }
        if last_link.elapsed() > LINK_TIMEOUT {
            link_up = false;
        }

        if let Some((ssid, pass)) = pending_wifi.take() {
            match connect_wifi(&mut wifi, &mut modem, &sysloop, &nvs, &ssid, &pass) {
                Ok(()) => {
                    if !sntp_on {
                        start_sntp();
                        sntp_on = true;
                    }
                }
                Err(err) => log::warn!("wifi: {err}"),
            }
        }

        while let Ok(event) = phone_rx.try_recv() {
            match event {
                Phone::Text(line) => {
                    let reply = on_text(&line, &mut shell, &nvs, &mut pending_wifi, &mut link);
                    notify_text(&gatt, reply.as_bytes());
                }
                Phone::OtaControl(bytes) => {
                    on_ota_control(&bytes, &mut session, &mut flash, &mut link);
                    notify_ota(&gatt, &session);
                }
                Phone::OtaData { seq, bytes } => {
                    on_ota_data(seq, bytes, &mut session, &mut flash, &mut link);
                    notify_ota(&gatt, &session);
                }
            }
        }

        let now_ms = boot.elapsed().as_millis() as u64;
        pending_detent += encoder.update(encoder_a.is_high(), encoder_b.is_high(), now_ms);
        pending_detent += remote_knob;
        remote_knob = 0;
        read_mic(
            &mut mic_in,
            &mut mic_scratch,
            &mut mic_pcm,
            &mut mic_at,
            &mut bands,
        );
        if last_frame.elapsed() < std::time::Duration::from_millis(16) {
            FreeRtos::delay_ms(2);
            continue;
        }
        last_frame = Instant::now();

        if last_battery.elapsed() >= std::time::Duration::from_millis(500) {
            if let Ok(raw) = battery_pin.read_raw() {
                battery_mv = millivolts(raw);
                battery_pct = percent(battery_mv);
            }
            last_battery = Instant::now();
        }
        if _sd_mount.is_some() && last_sd.elapsed() >= std::time::Duration::from_secs(2) {
            sd_entries = list_sd();
            last_sd = Instant::now();
        }
        let world = World {
            now_ms,
            unix: unix_now(),
            bands: &bands,
            battery_mv,
            battery_pct,
            sd: &sd_entries,
            bt,
            play,
            track: &track,
        };

        let detent = pending_detent;
        pending_detent = 0;
        if detent != 0 {
            let _ = i2c_effect(&mut i2c, STRONG_CLICK);
            dispatch(
                &mut shell.knob(detent, &world),
                &mut i2c,
                &mut link,
                &gatt,
                &mut release_hid,
                &mut tone_hz,
            );
        }
        if touch_irq.is_low() {
            if let Some(report) = read_touch(&mut i2c) {
                dispatch(
                    &mut shell.touch(report, &world),
                    &mut i2c,
                    &mut link,
                    &gatt,
                    &mut release_hid,
                    &mut tone_hz,
                );
            }
        } else {
            let idle = TouchReport {
                gesture: None,
                point: None,
            };
            let _ = shell.touch(idle, &world);
        }
        let tick = shell.tick(&world);
        dispatch(
            &tick,
            &mut i2c,
            &mut link,
            &gatt,
            &mut release_hid,
            &mut tone_hz,
        );
        tone_hz = tick.tone_hz;
        if sent_tone != tone_hz {
            send_msg(
                &mut link,
                &Msg::Tone {
                    hz: tone_hz.unwrap_or(0),
                },
            );
            sent_tone = tone_hz;
        }

        if release_hid {
            gatt.hid.lock().set_value(&hid::release()).notify();
            release_hid = false;
        }

        if let Some((y0, y1)) = shell.take_dirty() {
            if let Err(err) = blit(&mut panel, shell.canvas().pixels(), y0, y1, &mut strip) {
                log::warn!("blit: {err}");
                shell.mark_all_dirty();
            }
        }

        if last_status.elapsed() >= std::time::Duration::from_secs(1) {
            let app = shell.current_id().unwrap_or("").to_string();
            let line = ble::format_status(&ble::Status {
                firmware: FIRMWARE_ID_S3,
                app,
                uptime_s: (now_ms / 1000) as u32,
                battery_mv,
                link_up,
                bt: bt_label(bt),
            });
            gatt.status.lock().set_value(line.as_bytes()).notify();
            last_status = Instant::now();
        }

        FreeRtos::delay_ms(2);
    }
}

struct Gatt {
    text: std::sync::Arc<esp32_nimble::utilities::mutex::Mutex<BLECharacteristic>>,
    status: std::sync::Arc<esp32_nimble::utilities::mutex::Mutex<BLECharacteristic>>,
    ota_status: std::sync::Arc<esp32_nimble::utilities::mutex::Mutex<BLECharacteristic>>,
    hid: std::sync::Arc<esp32_nimble::utilities::mutex::Mutex<BLECharacteristic>>,
}

fn start_radio() -> anyhow::Result<Gatt> {
    let device = BLEDevice::take();
    let _ = device.set_preferred_mtu(256);
    let server = device.get_server();
    let advertising = device.get_advertising();
    server.on_connect(|server, desc| {
        log::info!("ble connected");
        let _ = server.update_conn_params(desc.conn_handle(), 12, 24, 0, 200);
    });
    server.on_disconnect(move |_desc, _reason| {
        log::info!("ble disconnected");
        let _ = advertising.lock().start();
    });

    let service = server.create_service(uuid_or_panic(ble::SERVICE_UUID));
    let info = service
        .lock()
        .create_characteristic(uuid_or_panic(ble::INFO_UUID), NimbleProperties::READ);
    info.lock()
        .set_value(&ble::encode_info(FIRMWARE_ID_S3, board::APP_SLOT_S3));

    let text = service.lock().create_characteristic(
        uuid_or_panic(ble::TEXT_UUID),
        NimbleProperties::READ | NimbleProperties::WRITE | NimbleProperties::NOTIFY,
    );
    text.lock().on_write(|args| {
        let line = String::from_utf8_lossy(args.recv_data()).into_owned();
        if let Some(tx) = PHONE.get() {
            if let Ok(tx) = tx.lock() {
                let _ = tx.send(Phone::Text(line));
            }
        }
    });

    let status = service.lock().create_characteristic(
        uuid_or_panic(ble::STATUS_UUID),
        NimbleProperties::READ | NimbleProperties::NOTIFY,
    );
    let ota_control = service.lock().create_characteristic(
        uuid_or_panic(ble::OTA_CONTROL_UUID),
        NimbleProperties::WRITE,
    );
    ota_control.lock().on_write(|args| {
        let bytes = args.recv_data().to_vec();
        if let Some(tx) = PHONE.get() {
            if let Ok(tx) = tx.lock() {
                let _ = tx.send(Phone::OtaControl(bytes));
            }
        }
    });
    let ota_data = service.lock().create_characteristic(
        uuid_or_panic(ble::OTA_DATA_UUID),
        NimbleProperties::WRITE | NimbleProperties::WRITE_NO_RSP,
    );
    ota_data.lock().on_write(|args| {
        let raw = args.recv_data();
        if let Ok((seq, chunk)) = ota::parse_chunk(raw) {
            if chunk.len() <= ble::MAX_OTA_CHUNK {
                if let Some(tx) = PHONE.get() {
                    if let Ok(tx) = tx.lock() {
                        let _ = tx.send(Phone::OtaData {
                            seq,
                            bytes: chunk.to_vec(),
                        });
                    }
                }
            }
        }
    });
    let ota_status = service.lock().create_characteristic(
        uuid_or_panic(ble::OTA_STATUS_UUID),
        NimbleProperties::READ | NimbleProperties::NOTIFY,
    );
    ota_status
        .lock()
        .set_value(&ble::encode_ota_status(&OtaSession::new()));
    let hid = service.lock().create_characteristic(
        uuid_or_panic(ble::HID_UUID),
        NimbleProperties::READ | NimbleProperties::NOTIFY,
    );
    hid.lock().set_value(&hid::release());

    let mut adv = BLEAdvertisementData::new();
    adv.name(DEVICE_NAME)
        .add_service_uuid(uuid_or_panic(ble::SERVICE_UUID));
    advertising.lock().set_data(&mut adv)?;
    advertising.lock().start()?;
    log::info!("advertising as {DEVICE_NAME}");

    Ok(Gatt {
        text,
        status,
        ota_status,
        hid,
    })
}

fn uuid_or_panic(text: &str) -> BleUuid {
    match text {
        ble::SERVICE_UUID => uuid128!("7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1001"),
        ble::INFO_UUID => uuid128!("7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1002"),
        ble::TEXT_UUID => uuid128!("7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1003"),
        ble::STATUS_UUID => uuid128!("7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1004"),
        ble::OTA_CONTROL_UUID => uuid128!("7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1005"),
        ble::OTA_DATA_UUID => uuid128!("7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1006"),
        ble::OTA_STATUS_UUID => uuid128!("7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1007"),
        ble::HID_UUID => uuid128!("7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1008"),
        other => panic!("unknown uuid {other}"),
    }
}

fn notify_text(gatt: &Gatt, bytes: &[u8]) {
    gatt.text.lock().set_value(bytes).notify();
}

fn notify_ota(gatt: &Gatt, session: &OtaSession) {
    gatt.ota_status
        .lock()
        .set_value(&ble::encode_ota_status(session))
        .notify();
}

fn on_text(
    line: &str,
    shell: &mut Shell,
    nvs: &EspDefaultNvsPartition,
    pending_wifi: &mut Option<(String, String)>,
    link: &mut UartDriver,
) -> String {
    let world = World::empty();
    match ble::parse_text(line) {
        Ok(TextCmd::Ping) => "pong".into(),
        Ok(TextCmd::Apps) => ble::reply_apps(&shell.ids()),
        Ok(TextCmd::Open(id)) => {
            if shell.open_id(&id, &world) {
                format!("open {id}")
            } else {
                format!("missing {id}")
            }
        }
        Ok(TextCmd::Status) => String::new(),
        Ok(TextCmd::Reboot(ble::ChipId::S3)) => {
            log::info!("reboot s3");
            unsafe { sys::esp_restart() }
        }
        Ok(TextCmd::Reboot(ble::ChipId::Esp32)) => {
            send_msg(link, &Msg::Reboot);
            "reboot esp32".into()
        }
        Ok(TextCmd::Wifi { ssid, pass }) => {
            if let Err(err) = save_wifi(nvs, &ssid, &pass) {
                return format!("wifi err {err}");
            }
            *pending_wifi = Some((ssid, pass));
            "wifi saved".into()
        }
        Err(_) => "err".into(),
    }
}

fn on_ota_control(
    bytes: &[u8],
    session: &mut OtaSession,
    flash: &mut Option<EspOtaUpdate<'static>>,
    link: &mut UartDriver,
) {
    if bytes.is_empty() {
        return;
    }
    match bytes[0] {
        opcode::BEGIN => match ota::parse_begin(bytes) {
            Ok((target, size, crc)) => {
                abort_flash(flash);
                if target == OtaTarget::Esp32 {
                    send_msg(link, &Msg::OtaAbort);
                }
                if let Err(err) = session.begin(target, size, crc) {
                    log::warn!("ota begin: {err:?}");
                    return;
                }
                if target == OtaTarget::S3 {
                    match start_local_flash() {
                        Ok(update) => *flash = Some(update),
                        Err(err) => {
                            log::warn!("ota flash: {err}");
                            session.note_error(ota::OtaError::State);
                        }
                    }
                } else {
                    send_msg(link, &Msg::OtaBegin { size, crc });
                }
            }
            Err(err) => session.note_error(err),
        },
        opcode::ABORT => {
            abort_flash(flash);
            send_msg(link, &Msg::OtaAbort);
            session.abort();
        }
        opcode::FINISH => match session.finish() {
            Ok(OtaTarget::S3) => {
                if let Some(update) = flash.take() {
                    if let Err(err) = update.complete() {
                        log::warn!("ota complete: {err}");
                    }
                }
            }
            Ok(OtaTarget::Esp32) => send_msg(link, &Msg::OtaFinish),
            Err(err) => {
                abort_flash(flash);
                send_msg(link, &Msg::OtaAbort);
                log::warn!("ota finish: {err:?}");
            }
        },
        opcode::REBOOT => match session.target() {
            Some(OtaTarget::Esp32) => send_msg(link, &Msg::Reboot),
            _ => unsafe { sys::esp_restart() },
        },
        opcode::MARK_VALID => {
            let _ = EspOta::new().and_then(|mut ota| ota.mark_running_slot_valid());
        }
        _ => session.note_error(ota::OtaError::State),
    }
}

fn on_ota_data(
    seq: u16,
    bytes: Vec<u8>,
    session: &mut OtaSession,
    flash: &mut Option<EspOtaUpdate<'static>>,
    link: &mut UartDriver,
) {
    if let Err(err) = session.push(seq, &bytes) {
        log::warn!("ota chunk: {err:?}");
        return;
    }
    match session.target() {
        Some(OtaTarget::S3) => {
            if let Some(update) = flash.as_mut() {
                if let Err(err) = update.write(&bytes) {
                    log::warn!("ota write: {err}");
                    session.note_error(ota::OtaError::State);
                }
            }
        }
        Some(OtaTarget::Esp32) => {
            send_msg(link, &Msg::OtaChunk { seq, data: bytes });
        }
        None => {}
    }
}

fn start_local_flash() -> Result<EspOtaUpdate<'static>, esp_idf_svc::sys::EspError> {
    let ota: &'static mut EspOta = Box::leak(Box::new(EspOta::new()?));
    ota.initiate_update()
}

fn abort_flash(flash: &mut Option<EspOtaUpdate<'static>>) {
    if let Some(update) = flash.take() {
        let _ = update.abort();
    }
}

fn dispatch(
    fx: &apps::Effects,
    i2c: &mut I2cDriver,
    link: &mut UartDriver,
    gatt: &Gatt,
    release_hid: &mut bool,
    _tone_hz: &mut Option<u16>,
) {
    if let Some(effect) = fx.haptic {
        let _ = i2c_effect(i2c, effect);
    }
    if let Some(usage) = fx.consumer {
        gatt.hid.lock().set_value(&hid::report(usage)).notify();
        *release_hid = true;
    }
    for msg in &fx.link {
        send_msg(link, msg);
    }
}

fn i2c_effect(i2c: &mut I2cDriver, effect: u8) -> Result<(), esp_idf_svc::sys::EspError> {
    for write in haptic::play(effect) {
        i2c.write(haptic::ADDR, &[write.reg, write.val], BLOCK)?;
    }
    Ok(())
}

fn read_touch(i2c: &mut I2cDriver) -> Option<TouchReport> {
    let mut buf = [0u8; 6];
    i2c.write_read(board::s3::TOUCH_ADDR, &[0x00], &mut buf, BLOCK)
        .ok()?;
    touch::parse_report(&buf).ok()
}

fn read_mic(
    mic_in: &mut I2sDriver<I2sRx>,
    scratch: &mut [u8],
    pcm: &mut [i16; 512],
    at: &mut usize,
    bands: &mut [u8],
) {
    let n = mic_in.read(scratch, NON_BLOCK).unwrap_or(0);
    if n < 2 {
        return;
    }
    let samples = &scratch[..n - (n % 2)];
    for chunk in samples.chunks_exact(2) {
        if *at >= pcm.len() {
            break;
        }
        pcm[*at] = i16::from_le_bytes([chunk[0], chunk[1]]);
        *at += 1;
    }
    if *at == pcm.len() {
        mic::bands_into(pcm, bands);
        *at = 0;
    }
}

fn read_link(
    uart: &mut UartDriver,
    buf: &mut [u8],
    decoder: &mut Decoder,
    out: &mut Vec<Msg>,
    decoded: &mut Vec<Result<Msg, knob::link::LinkError>>,
) {
    out.clear();
    loop {
        let n = match uart.read(buf, NON_BLOCK) {
            Ok(0) | Err(_) => break,
            Ok(n) => n,
        };
        decoded.clear();
        decoder.drain_into(&buf[..n], decoded);
        for item in decoded.drain(..) {
            if let Ok(msg) = item {
                out.push(msg);
            }
        }
        if n < buf.len() {
            break;
        }
    }
}

fn send_msg(uart: &mut UartDriver, msg: &Msg) {
    let mut frame = [0u8; link::MAX_FRAME];
    let Ok(n) = link::encode_into(msg, &mut frame) else {
        return;
    };
    let frame = &frame[..n];
    let mut off = 0;
    while off < frame.len() {
        match uart.write(&frame[off..]) {
            Ok(0) | Err(_) => break,
            Ok(n) => off += n,
        }
    }
}

fn init_panel<'d>(dev: &mut SpiDeviceDriver<'d, SpiDriver<'d>>) -> anyhow::Result<()> {
    for cmd in st77916::INIT {
        lcd_cmd(dev, cmd.cmd, cmd.data)?;
        if cmd.delay_ms > 0 {
            FreeRtos::delay_ms(cmd.delay_ms as u32);
        }
    }
    Ok(())
}

fn lcd_cmd<'d>(
    dev: &mut SpiDeviceDriver<'d, SpiDriver<'d>>,
    cmd: u8,
    data: &[u8],
) -> anyhow::Result<()> {
    let header = st77916::header(st77916::CMD_WRITE, cmd);
    if data.is_empty() {
        dev.transaction(&mut [Operation::Write(&header)])?;
    } else {
        dev.transaction(&mut [Operation::Write(&header), Operation::Write(data)])?;
    }
    Ok(())
}

fn blit<'d>(
    dev: &mut SpiDeviceDriver<'d, SpiDriver<'d>>,
    pixels: &[u16],
    y0: u16,
    y1: u16,
    strip: &mut [u8],
) -> anyhow::Result<()> {
    let width = usize::from(PANEL_W);
    let rows = 4usize;
    let mut y = y0;
    while y <= y1 {
        let row_end = (y as usize + rows - 1).min(usize::from(y1)) as u16;
        let [xs, ys] = st77916::caset_raset(0, y, PANEL_W - 1, row_end);
        lcd_cmd(dev, CASET, &xs)?;
        lcd_cmd(dev, RASET, &ys)?;
        let start = usize::from(y) * width;
        let end = (usize::from(row_end) + 1) * width;
        let mut n = 0;
        for px in &pixels[start..end] {
            let be = px.to_be_bytes();
            strip[n] = be[0];
            strip[n + 1] = be[1];
            n += 2;
        }
        let header = st77916::header(st77916::COLOR_QIO, RAMWR);
        dev.transaction(&mut [
            Operation::Write(&header),
            Operation::WriteWithWidth(&strip[..n], LineWidth::Quad),
        ])?;
        if row_end == y1 {
            break;
        }
        y = row_end + 1;
    }
    Ok(())
}

fn list_sd() -> Vec<SdEntry> {
    let mut dir: sys::FF_DIR = unsafe { core::mem::zeroed() };
    let path = c"0:/";
    if unsafe { sys::f_opendir(&mut dir, path.as_ptr()) } != 0 {
        return Vec::new();
    }
    let mut out = Vec::new();
    loop {
        let mut info: sys::FILINFO = unsafe { core::mem::zeroed() };
        if unsafe { sys::f_readdir(&mut dir, &mut info) } != 0 {
            break;
        }
        let raw = unsafe {
            core::slice::from_raw_parts(
                info.fname.as_ptr() as *const u8,
                core::mem::size_of_val(&info.fname),
            )
        };
        let end = raw.iter().position(|b| *b == 0).unwrap_or(raw.len());
        if end == 0 {
            break;
        }
        let name = String::from_utf8_lossy(&raw[..end]).into_owned();
        if name == "." || name == ".." {
            continue;
        }
        let dir_bit = info.fattrib & 0x10 != 0;
        out.push(SdEntry {
            name,
            bytes: info.fsize as u64,
            dir: dir_bit,
        });
        if out.len() == 32 {
            break;
        }
    }
    unsafe { sys::f_closedir(&mut dir) };
    if out.is_empty() {
        out.push(SdEntry {
            name: "/".into(),
            bytes: 0,
            dir: true,
        });
    }
    out
}

fn load_wifi(nvs: &EspDefaultNvsPartition) -> Option<(String, String)> {
    let ns = EspNvs::new(nvs.clone(), "knob", false).ok()?;
    let mut ssid_buf = [0u8; 33];
    let mut pass_buf = [0u8; 65];
    let ssid = ns
        .get_str("ssid", &mut ssid_buf)
        .ok()
        .flatten()?
        .to_string();
    let pass = ns
        .get_str("pass", &mut pass_buf)
        .ok()
        .flatten()?
        .to_string();
    if ssid.is_empty() {
        None
    } else {
        Some((ssid, pass))
    }
}

fn save_wifi(nvs: &EspDefaultNvsPartition, ssid: &str, pass: &str) -> anyhow::Result<()> {
    let ns = EspNvs::new(nvs.clone(), "knob", true)?;
    ns.set_str("ssid", ssid)?;
    ns.set_str("pass", pass)?;
    Ok(())
}

fn connect_wifi(
    slot: &mut Option<BlockingWifi<EspWifi<'static>>>,
    modem: &mut Option<Modem<'static>>,
    sysloop: &EspSystemEventLoop,
    nvs: &EspDefaultNvsPartition,
    ssid: &str,
    pass: &str,
) -> anyhow::Result<()> {
    if slot.is_none() {
        let taken = modem
            .take()
            .ok_or_else(|| anyhow::anyhow!("wifi modem already used"))?;
        let wifi = EspWifi::new(taken, sysloop.clone(), Some(nvs.clone()))?;
        *slot = Some(BlockingWifi::wrap(wifi, sysloop.clone())?);
    }
    let wifi = slot.as_mut().unwrap();
    let auth = if pass.is_empty() {
        AuthMethod::None
    } else {
        AuthMethod::WPA2Personal
    };
    wifi.set_configuration(&WifiConfig::Client(ClientConfiguration {
        ssid: ssid.try_into().map_err(|_| anyhow::anyhow!("ssid"))?,
        password: pass.try_into().map_err(|_| anyhow::anyhow!("pass"))?,
        auth_method: auth,
        ..Default::default()
    }))?;
    wifi.start()?;
    wifi.connect()?;
    wifi.wait_netif_up()?;
    log::info!("wifi up");
    Ok(())
}

fn start_sntp() {
    unsafe {
        sys::esp_sntp_setoperatingmode(sys::esp_sntp_operatingmode_t_ESP_SNTP_OPMODE_POLL);
        sys::esp_sntp_setservername(0, c"pool.ntp.org".as_ptr());
        sys::esp_sntp_init();
    }
}

fn unix_now() -> Option<u64> {
    let mut tv = sys::timeval {
        tv_sec: 0,
        tv_usec: 0,
    };
    unsafe { sys::gettimeofday(&mut tv, core::ptr::null_mut()) };
    if tv.tv_sec > 1_600_000_000 {
        Some(tv.tv_sec as u64)
    } else {
        None
    }
}

fn bt_label(state: BtState) -> &'static str {
    match state {
        BtState::Disconnected => "off",
        BtState::Discoverable => "pair",
        BtState::Connecting => "wait",
        BtState::Connected => "on",
    }
}
