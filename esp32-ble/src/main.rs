//! Playground BLE GATT server: LED commands in, status notifications out.

use std::sync::{Arc, Mutex};
use std::time::Instant;

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

/// Onboard LED on most ESP32-DevKitC boards. Change this if your board differs.
const LED_GPIO_LABEL: &str = "GPIO2";

/// True when a high pin level turns the LED on.
const LED_ACTIVE_HIGH: bool = true;

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    info!("{FIRMWARE_ID} starting ({LED_GPIO_LABEL}, active_high={LED_ACTIVE_HIGH})");

    let peripherals = Peripherals::take()?;
    let mut led = PinDriver::output(peripherals.pins.gpio2)?;
    drive_led(&mut led, false)?;

    let state = Arc::new(Mutex::new(DeviceState::default()));
    let started = Instant::now();

    let device = BLEDevice::take();
    let server = device.get_server();
    let advertising = device.get_advertising();

    server.on_connect(|server, desc| {
        info!("connected: {desc:?}");
        if let Err(err) = server.update_conn_params(desc.conn_handle(), 24, 48, 0, 60) {
            info!("update_conn_params: {err:?}");
        }
    });
    server.on_disconnect(|_desc, reason| {
        info!("disconnected: {reason:?}");
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

    let mut adv = BLEAdvertisementData::new()
        .name(DEVICE_NAME)
        .add_service_uuid(uuid_or_panic(SERVICE_UUID));
    advertising.lock().set_data(&mut adv)?;
    advertising.lock().start()?;
    info!("advertising as {DEVICE_NAME}");

    let mut last_line = String::new();
    let mut last_notify = Instant::now();
    loop {
        FreeRtos::delay_ms(50);
        let elapsed_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
        let snapshot = state.lock().expect("state").clone();
        drive_led(&mut led, snapshot.physical_led_on(elapsed_ms))?;

        let line = format_status(&snapshot.to_status(elapsed_ms, heap_free()));
        let due = last_notify.elapsed().as_millis() >= 500;
        if due || line != last_line {
            status.lock().set_value(line.as_bytes()).notify();
            last_line = line;
            last_notify = Instant::now();
        }
    }
}

// esp-idf-hal 0.46 uses PinDriver<'d, MODE>. The pin type is erased into MODE.
fn drive_led(led: &mut PinDriver<'_, Output>, on: bool) -> Result<()> {
    let level = if LED_ACTIVE_HIGH { on } else { !on };
    if level {
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
