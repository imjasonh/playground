//! Playground BLE GATT server: LED commands in, status notifications out.

use std::sync::{Arc, Mutex};

use anyhow::Result;
use esp32_ble::protocol::{
    encode_command, format_status, parse_command, DeviceState, COMMAND_UUID, DEVICE_NAME,
    FIRMWARE_ID, SERVICE_UUID, STATUS_UUID,
};
use esp32_nimble::utilities::BleUuid;
use esp32_nimble::{uuid128, BLEAdvertisementData, BLEDevice, NimbleProperties};
use esp_idf_svc::hal::delay::FreeRtos;
use esp_idf_svc::hal::gpio::{Output, PinDriver};
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::sys::esp_get_free_heap_size;
use log::info;

/// Command LED is GPIO 2, the D2 pad on the Inland / Keyestudio core board.
/// D1 on that board is power only and cannot be toggled.
const LED_GPIO_LABEL: &str = "GPIO2";

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    info!("{FIRMWARE_ID} starting ({LED_GPIO_LABEL}; Inland D1 is power-only)");

    let peripherals = Peripherals::take()?;
    let mut led = PinDriver::output(peripherals.pins.gpio2)?;
    drive_led(&mut led, true)?;

    let state = Arc::new(Mutex::new(DeviceState::default()));

    let device = BLEDevice::take();
    let server = device.get_server();
    let advertising = device.get_advertising();

    server.on_connect(|server, desc| {
        info!("connected: {desc:?}");
        if let Err(err) = server.update_conn_params(desc.conn_handle(), 24, 48, 0, 60) {
            info!("update_conn_params: {err:?}");
        }
    });
    server.on_disconnect(move |_desc, reason| {
        info!("disconnected: {reason:?}");
        if let Err(err) = advertising.lock().start() {
            info!("restart advertising: {err:?}");
        }
    });

    let service = server.create_service(uuid_or_panic(SERVICE_UUID));

    let command = service
        .lock()
        .create_characteristic(uuid_or_panic(COMMAND_UUID), NimbleProperties::WRITE);
    let status = service.lock().create_characteristic(
        uuid_or_panic(STATUS_UUID),
        NimbleProperties::READ | NimbleProperties::NOTIFY,
    );

    {
        let initial = format_status(&state.lock().expect("state").to_status(0, heap_free()));
        status.lock().set_value(initial.as_bytes());
    }

    let write_state = Arc::clone(&state);
    command.lock().on_write(move |args| {
        let raw = String::from_utf8_lossy(args.recv_data());
        info!("command write: {raw}");
        let mut guard = write_state.lock().expect("state");
        match parse_command(raw.as_ref()) {
            Some(parsed) => {
                guard.apply(parsed);
                info!("applied {}", encode_command(parsed));
            }
            None => {
                info!("ignored unrecognized command");
                guard.last_command = format!("? {}", raw.trim());
            }
        }
    });

    let mut adv = BLEAdvertisementData::new();
    adv.name(DEVICE_NAME)
        .add_service_uuid(uuid_or_panic(SERVICE_UUID));
    advertising.lock().set_data(&mut adv)?;
    advertising.lock().start()?;
    info!("advertising as {DEVICE_NAME}");

    let mut last_line = String::new();
    let mut elapsed_ms: u64 = 0;
    let mut last_notify_ms: u64 = 0;
    loop {
        FreeRtos::delay_ms(50);
        elapsed_ms = elapsed_ms.saturating_add(50);
        let snapshot = state.lock().expect("state").clone();
        drive_led(&mut led, snapshot.physical_led_on(elapsed_ms))?;

        let line = format_status(&snapshot.to_status(elapsed_ms, heap_free()));
        let due = elapsed_ms.saturating_sub(last_notify_ms) >= 500;
        if due || line != last_line {
            status.lock().set_value(line.as_bytes()).notify();
            last_line = line;
            last_notify_ms = elapsed_ms;
        }
    }
}

// esp-idf-hal 0.46 uses PinDriver<'d, MODE>. The pin type is erased into MODE.
fn drive_led(led: &mut PinDriver<'_, Output>, on: bool) -> Result<()> {
    if on {
        led.set_high()?;
    } else {
        led.set_low()?;
    }
    Ok(())
}

fn heap_free() -> Option<u32> {
    Some(unsafe { esp_get_free_heap_size() })
}

fn uuid_or_panic(text: &str) -> BleUuid {
    // Keep these literals identical to `protocol.rs`. The macro parses at
    // compile time; the match is a guard so a drift fails the firmware build.
    match text {
        SERVICE_UUID => uuid128!("4fafc201-1fb5-459e-8fcc-c5c9c331914b"),
        COMMAND_UUID => uuid128!("beb5483e-36e1-4688-b7f5-ea07361b26a6"),
        STATUS_UUID => uuid128!("1a3c0001-36e1-4688-b7f5-ea07361b26a6"),
        other => panic!("unknown UUID {other}"),
    }
}
