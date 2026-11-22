//! Shared BLE Manufacturer Data broadcaster + on-demand BLE GATT OTA server.
//!
//! `BleOtaNode` registers the GATT service once at boot and can be called once
//! per wake (deep-sleep boards like XIAO ESP32-C3) or repeatedly in a loop
//! (USB-powered boards like the Waveshare 7.5″ e-Paper ESP32).

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use esp32_nimble::enums::ConnMode;
use esp32_nimble::utilities::BleUuid;
use esp32_nimble::{uuid128, BLEAdvertisementData, BLECharacteristic, BLEDevice, NimbleProperties};
use esp_idf_svc::hal::delay::FreeRtos;
use esp_idf_svc::sys::{
    esp_ota_abort, esp_ota_begin, esp_ota_end, esp_ota_get_next_update_partition,
    esp_ota_get_running_partition, esp_ota_get_state_partition, esp_ota_handle_t,
    esp_ota_img_states_t, esp_ota_img_states_t_ESP_OTA_IMG_PENDING_VERIFY,
    esp_ota_mark_app_valid_cancel_rollback, esp_ota_set_boot_partition, esp_ota_write,
    esp_partition_t, esp_restart, ESP_OK,
};
use log::{info, warn};
use sha2::{Digest, Sha256};

use crate::profiler::{create_profile_char, now_us, update_profile_char, ProfileCharHandle};
use crate::protocol::{
    encode_mfg_data, format_ota_status, parse_ota_command, validate_esp_image_header, AdvMetrics,
    BoardConfig, OtaCommand, OtaStatus, OTA_CONTROL_UUID, OTA_DATA_UUID, OTA_SERVICE_UUID,
    OTA_SLOT_BYTES, OTA_STATUS_UUID,
};

/// Maximum time an active BLE OTA connection may keep the board awake before timing out (120 s).
const OTA_SESSION_TIMEOUT_MS: u32 = 120_000;

/// Maximum idle time on an open BLE connection without any OTA control/data write (15 s).
const OTA_IDLE_TIMEOUT_US: u64 = 15_000_000;

/// Check if the running OTA partition is in `ESP_OTA_IMG_PENDING_VERIFY` and mark it valid.
pub fn mark_ota_slot_valid_if_pending() {
    // SAFETY: esp_ota_get_running_partition, esp_ota_get_state_partition, and
    // esp_ota_mark_app_valid_cancel_rollback are thread-safe ESP-IDF C APIs.
    unsafe {
        let part = esp_ota_get_running_partition();
        if part.is_null() {
            return;
        }
        let mut state: esp_ota_img_states_t = 0;
        if esp_ota_get_state_partition(part, &mut state) == ESP_OK
            && state == esp_ota_img_states_t_ESP_OTA_IMG_PENDING_VERIFY
        {
            let err = esp_ota_mark_app_valid_cancel_rollback();
            if err == ESP_OK {
                info!("ota: marked new firmware slot valid (rollback cancelled)");
            } else {
                warn!("ota: mark_app_valid failed err={err}");
            }
        }
    }
}

struct OtaWriterState {
    expected_chip_id: u16,
    handle: Option<esp_ota_handle_t>,
    partition: *const esp_partition_t,
    expected_size: u32,
    expected_sha256: String,
    written: u32,
    next_notify_at: u32,
    last_activity_us: u64,
    hasher: Sha256,
    reboot_pending: bool,
}

// SAFETY: `partition` points to an immutable ESP-IDF partition descriptor table entry in flash/ROM.
unsafe impl Send for OtaWriterState {}

impl OtaWriterState {
    fn new(expected_chip_id: u16) -> Self {
        Self {
            expected_chip_id,
            handle: None,
            partition: core::ptr::null(),
            expected_size: 0,
            expected_sha256: String::new(),
            written: 0,
            next_notify_at: 0,
            last_activity_us: 0,
            hasher: Sha256::new(),
            reboot_pending: false,
        }
    }

    fn abort_active(&mut self) {
        if let Some(h) = self.handle.take() {
            // SAFETY: `h` was returned by `esp_ota_begin` and has not been ended yet.
            unsafe {
                let _ = esp_ota_abort(h);
            }
        }
        self.partition = core::ptr::null();
        self.expected_size = 0;
        self.expected_sha256.clear();
        self.written = 0;
        self.next_notify_at = 0;
        self.hasher = Sha256::new();
    }

    fn begin(&mut self, size: u32, sha256: String) -> OtaStatus {
        self.abort_active();
        self.last_activity_us = now_us();
        if size == 0 || size > OTA_SLOT_BYTES {
            return OtaStatus::Error {
                message: format!("invalid size {size}"),
            };
        }
        // SAFETY: queries ESP-IDF's partition table for the inactive OTA app slot and opens it.
        unsafe {
            let part = esp_ota_get_next_update_partition(core::ptr::null());
            if part.is_null() {
                return OtaStatus::Error {
                    message: "no inactive OTA slot (run make flash-all)".to_string(),
                };
            }
            let mut handle: esp_ota_handle_t = 0;
            let err = esp_ota_begin(part, size as usize, &mut handle);
            if err != ESP_OK {
                return OtaStatus::Error {
                    message: format!("esp_ota_begin err={err}"),
                };
            }
            self.handle = Some(handle);
            self.partition = part;
            self.expected_size = size;
            self.expected_sha256 = sha256;
            self.written = 0;
            self.next_notify_at = 16 * 1024;
            self.hasher = Sha256::new();
            info!("ota: opened inactive partition for {size} bytes");
            OtaStatus::Ready { total: size }
        }
    }

    fn write_chunk(&mut self, chunk: &[u8]) -> Option<OtaStatus> {
        self.last_activity_us = now_us();
        let Some(handle) = self.handle else {
            return Some(OtaStatus::Error {
                message: "write before BEGIN".to_string(),
            });
        };
        if chunk.is_empty() {
            return None;
        }
        if self.written == 0 {
            if let Err(msg) = validate_esp_image_header(chunk, self.expected_chip_id) {
                self.abort_active();
                return Some(OtaStatus::Error { message: msg });
            }
        }
        let next_written = self.written.saturating_add(chunk.len() as u32);
        if next_written > self.expected_size {
            self.abort_active();
            return Some(OtaStatus::Error {
                message: format!("overflow: {next_written} > {}", self.expected_size),
            });
        }
        // SAFETY: `handle` is an active OTA handle and `chunk` is valid for `chunk.len()` bytes.
        let err = unsafe { esp_ota_write(handle, chunk.as_ptr().cast(), chunk.len()) };
        if err != ESP_OK {
            self.abort_active();
            return Some(OtaStatus::Error {
                message: format!("esp_ota_write err={err}"),
            });
        }
        self.hasher.update(chunk);
        self.written = next_written;
        if self.written >= self.next_notify_at || self.written == self.expected_size {
            self.next_notify_at = self.written.saturating_add(16 * 1024);
            return Some(OtaStatus::Progress {
                written: self.written,
                total: self.expected_size,
            });
        }
        None
    }

    fn commit(&mut self) -> OtaStatus {
        self.last_activity_us = now_us();
        let Some(handle) = self.handle.take() else {
            return OtaStatus::Error {
                message: "commit before BEGIN".to_string(),
            };
        };
        if self.written != self.expected_size {
            // SAFETY: `handle` was just taken and is still open.
            unsafe {
                let _ = esp_ota_abort(handle);
            }
            let w = self.written;
            let total = self.expected_size;
            self.abort_active();
            return OtaStatus::Error {
                message: format!("incomplete: {w}/{total} bytes"),
            };
        }
        let actual_sha = hex::encode(self.hasher.clone().finalize());
        if actual_sha != self.expected_sha256 {
            // SAFETY: `handle` was just taken and is still open.
            unsafe {
                let _ = esp_ota_abort(handle);
            }
            let expected = self.expected_sha256.clone();
            self.abort_active();
            return OtaStatus::Error {
                message: format!("sha256 mismatch: got {actual_sha}, want {expected}"),
            };
        }
        // SAFETY: finalizes the verified OTA image and switches `otadata` to boot `self.partition`.
        unsafe {
            let end_err = esp_ota_end(handle);
            if end_err != ESP_OK {
                self.abort_active();
                return OtaStatus::Error {
                    message: format!("esp_ota_end err={end_err}"),
                };
            }
            let boot_err = esp_ota_set_boot_partition(self.partition);
            if boot_err != ESP_OK {
                self.abort_active();
                return OtaStatus::Error {
                    message: format!("esp_ota_set_boot_partition err={boot_err}"),
                };
            }
        }
        info!("ota: committed {actual_sha}, rebooting into new slot");
        self.reboot_pending = true;
        OtaStatus::Ok { sha256: actual_sha }
    }
}

fn notify_ota_status(
    ch: &Arc<esp32_nimble::utilities::mutex::Mutex<BLECharacteristic>>,
    st: &OtaStatus,
) {
    let line = format_ota_status(st);
    info!("ota status: {line}");
    ch.lock().set_value(line.as_bytes()).notify();
}

/// Persistent NimBLE peripheral + OTA GATT server initialized once per boot.
pub struct BleOtaNode {
    board: BoardConfig,
    connected: Arc<AtomicBool>,
    ota_state: Arc<Mutex<OtaWriterState>>,
    profile_char: ProfileCharHandle,
}

impl BleOtaNode {
    /// Initialize NimBLE and register the OTA + Profile GATT service once.
    pub fn init(board: BoardConfig) -> Self {
        let device = BLEDevice::take();
        let _ = device.set_preferred_mtu(512);
        let server = device.get_server();

        let connected = Arc::new(AtomicBool::new(false));
        let ota_state = Arc::new(Mutex::new(OtaWriterState::new(board.chip_id)));

        let conn_on_connect = Arc::clone(&connected);
        let state_on_connect = Arc::clone(&ota_state);
        server.on_connect(move |server, desc| {
            state_on_connect.lock().expect("ota_state").last_activity_us = now_us();
            conn_on_connect.store(true, Ordering::SeqCst);
            info!("ble connected for OTA/profile: {desc:?}");
            // Fast 7.5 ms - 15 ms connection interval for high-throughput BLE OTA streaming.
            let _ = server.update_conn_params(desc.conn_handle(), 6, 12, 0, 200);
        });

        let conn_on_disconnect = Arc::clone(&connected);
        let state_on_disconnect = Arc::clone(&ota_state);
        server.on_disconnect(move |_desc, reason| {
            info!("ble disconnected: {reason:?}");
            state_on_disconnect
                .lock()
                .expect("ota_state")
                .abort_active();
            conn_on_disconnect.store(false, Ordering::SeqCst);
        });

        let service = server.create_service(uuid_or_panic(OTA_SERVICE_UUID));
        let control_char = service
            .lock()
            .create_characteristic(uuid_or_panic(OTA_CONTROL_UUID), NimbleProperties::WRITE);
        let data_char = service.lock().create_characteristic(
            uuid_or_panic(OTA_DATA_UUID),
            NimbleProperties::WRITE | NimbleProperties::WRITE_NO_RSP,
        );
        let status_char = service.lock().create_characteristic(
            uuid_or_panic(OTA_STATUS_UUID),
            NimbleProperties::READ | NimbleProperties::NOTIFY,
        );
        status_char
            .lock()
            .set_value(format_ota_status(&OtaStatus::Idle).as_bytes());

        let profile_char = create_profile_char(&service);

        let ctrl_state = Arc::clone(&ota_state);
        let ctrl_status_char = Arc::clone(&status_char);
        control_char.lock().on_write(move |args| {
            let raw = String::from_utf8_lossy(args.recv_data());
            info!("ota control write: {raw}");
            let mut guard = ctrl_state.lock().expect("ota_state");
            let reply = match parse_ota_command(raw.as_ref()) {
                Some(OtaCommand::Begin { size, sha256 }) => guard.begin(size, sha256),
                Some(OtaCommand::Commit) => guard.commit(),
                Some(OtaCommand::Abort) => {
                    guard.abort_active();
                    OtaStatus::Idle
                }
                None => OtaStatus::Error {
                    message: "invalid OTA command".to_string(),
                },
            };
            notify_ota_status(&ctrl_status_char, &reply);
        });

        let data_state = Arc::clone(&ota_state);
        let data_status_char = Arc::clone(&status_char);
        data_char.lock().on_write(move |args| {
            let chunk = args.recv_data();
            let mut guard = data_state.lock().expect("ota_state");
            if let Some(status) = guard.write_chunk(chunk) {
                notify_ota_status(&data_status_char, &status);
            }
        });

        Self {
            board,
            connected,
            ota_state,
            profile_char,
        }
    }

    /// Broadcast `metrics` inside BLE Manufacturer Specific Data (`0xFFFF`) for `burst_ms`.
    /// If an iPhone connects during that window to pull the WakeProfile or push an OTA image,
    /// stay awake until the session finishes, disconnects, or hits the timeout.
    pub fn broadcast_burst(&self, metrics: &AdvMetrics, profile_json: Option<&str>, burst_ms: u32) {
        update_profile_char(&self.profile_char, profile_json);

        let device = BLEDevice::take();
        let advertising = device.get_advertising();

        let mfg = encode_mfg_data(metrics);
        let mut adv = BLEAdvertisementData::new();
        adv.name(self.board.gap_name).manufacturer_data(&mfg);

        let mut guard = advertising.lock();
        guard
            .advertisement_type(ConnMode::Und)
            .scan_response(true)
            .min_interval(32)
            .max_interval(48);

        if let Err(err) = guard.set_data(&mut adv) {
            info!("ble set_data error: {err:?}");
            return;
        }
        if let Err(err) = guard.start() {
            info!("ble start error: {err:?}");
            return;
        }
        drop(guard);

        FreeRtos::delay_ms(burst_ms);

        if self.connected.load(Ordering::SeqCst) {
            info!("ota: iPhone connected during burst; holding awake for BLE OTA/profile");
            let mut waited_ms: u32 = 0;
            while self.connected.load(Ordering::SeqCst) && waited_ms < OTA_SESSION_TIMEOUT_MS {
                FreeRtos::delay_ms(50);
                waited_ms = waited_ms.saturating_add(50);
                let mut guard = self.ota_state.lock().expect("ota_state");
                if guard.reboot_pending {
                    drop(guard);
                    // Give NimBLE 250 ms to flush the final `OK sha256=...` notification before rebooting.
                    FreeRtos::delay_ms(250);
                    unsafe {
                        esp_restart();
                    }
                }
                if now_us().saturating_sub(guard.last_activity_us) > OTA_IDLE_TIMEOUT_US {
                    warn!("ota: idle timeout on BLE connection; aborting");
                    guard.abort_active();
                    break;
                }
            }
        }

        let _ = advertising.lock().stop();
    }
}

fn uuid_or_panic(text: &str) -> BleUuid {
    match text {
        OTA_SERVICE_UUID => uuid128!("4fafc301-1fb5-459e-8fcc-c5c9c331914b"),
        OTA_CONTROL_UUID => uuid128!("beb5483e-36e1-4688-b7f5-ea07361bc301"),
        OTA_DATA_UUID => uuid128!("beb5483e-36e1-4688-b7f5-ea07361bc302"),
        OTA_STATUS_UUID => uuid128!("1a3c0001-36e1-4688-b7f5-ea07361bc303"),
        other => panic!("unknown UUID {other}"),
    }
}
