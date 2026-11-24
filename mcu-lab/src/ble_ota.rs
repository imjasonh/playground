//! Shared BLE Manufacturer Data broadcaster, resumable BLE GATT OTA server,
//! and flash coredump uploader.
//!
//! `BleOtaNode` registers the GATT service once at boot and can be called once
//! per wake (deep-sleep boards like XIAO ESP32-C3) or repeatedly in a loop
//! (USB-powered boards like the Waveshare 7.5″ e-Paper ESP32).

use std::sync::atomic::{AtomicBool, AtomicU16, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

use esp32_nimble::enums::ConnMode;
use esp32_nimble::utilities::BleUuid;
use esp32_nimble::{uuid128, BLEAdvertisementData, BLECharacteristic, BLEDevice, NimbleProperties};
use esp_idf_svc::hal::delay::FreeRtos;
use esp_idf_svc::sys::{
    esp_core_dump_image_check, esp_core_dump_image_erase, esp_core_dump_image_get, esp_ota_abort,
    esp_ota_begin, esp_ota_end, esp_ota_get_next_update_partition, esp_ota_get_running_partition,
    esp_ota_get_state_partition, esp_ota_handle_t, esp_ota_img_states_t,
    esp_ota_img_states_t_ESP_OTA_IMG_PENDING_VERIFY, esp_ota_mark_app_invalid_rollback_and_reboot,
    esp_ota_mark_app_valid_cancel_rollback, esp_ota_set_boot_partition, esp_ota_write,
    esp_partition_find_first, esp_partition_read,
    esp_partition_subtype_t_ESP_PARTITION_SUBTYPE_DATA_COREDUMP, esp_partition_t,
    esp_partition_type_t_ESP_PARTITION_TYPE_DATA, esp_restart, esp_task_wdt_reset, ESP_OK,
    OTA_WITH_SEQUENTIAL_WRITES,
};
use log::{info, warn};
use sha2::{Digest, Sha256};

use crate::profiler::{create_profile_char, now_us, update_profile_char, ProfileCharHandle};
use crate::protocol::{
    decode_ota_chunk_frame, encode_blob_frames, encode_mfg_data, format_ota_status,
    parse_app_command, parse_ota_command, validate_esp_image_header, AdvMetrics, AppCommandRequest,
    BoardSpec, OtaCommand, OtaCompression, OtaDeflateDecoder, OtaStatus, APP_COMMAND_CHAR_UUID,
    COREDUMP_CHAR_UUID, OTA_CONTROL_UUID, OTA_DATA_UUID, OTA_SERVICE_UUID, OTA_SLOT_BYTES,
    OTA_STATUS_UUID,
};

/// Maximum time an active BLE OTA connection may keep the board awake before timing out (300 s).
const OTA_SESSION_TIMEOUT_MS: u32 = 300_000;

/// Maximum idle time on an open BLE connection without any OTA control/data write (15 s).
const OTA_IDLE_TIMEOUT_US: u64 = 15_000_000;

/// Maximum payload bytes per BLE GATT coredump notification frame.
const COREDUMP_CHUNK_PAYLOAD: usize = 460;

/// Acquire a mutex without panicking inside NimBLE callbacks if a prior panic poisoned it.
fn lock_or_recover<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Returns `true` if the currently running OTA slot is in `ESP_OTA_IMG_PENDING_VERIFY`.
pub fn is_ota_slot_pending_verify() -> bool {
    // SAFETY: ESP-IDF OTA partition query APIs are thread-safe.
    unsafe {
        let part = esp_ota_get_running_partition();
        if part.is_null() {
            return false;
        }
        let mut state: esp_ota_img_states_t = 0;
        esp_ota_get_state_partition(part, &mut state) == ESP_OK
            && state == esp_ota_img_states_t_ESP_OTA_IMG_PENDING_VERIFY
    }
}

/// Check if the running OTA partition is in `ESP_OTA_IMG_PENDING_VERIFY` and mark it valid.
pub fn mark_ota_slot_valid_if_pending() {
    if !is_ota_slot_pending_verify() {
        return;
    }
    // SAFETY: `esp_ota_mark_app_valid_cancel_rollback` is a thread-safe ESP-IDF C API.
    let err = unsafe { esp_ota_mark_app_valid_cancel_rollback() };
    if err == ESP_OK {
        info!("ota: marked new firmware slot valid (rollback cancelled)");
    } else {
        warn!("ota: mark_app_valid failed err={err}");
    }
}

/// Mark the running `PENDING_VERIFY` slot invalid and reboot into the previous known-good slot.
pub fn rollback_ota_slot_and_reboot() {
    if !is_ota_slot_pending_verify() {
        return;
    }
    warn!("ota: marking PENDING_VERIFY slot invalid and rolling back");
    // SAFETY: transitions otadata back to the previous valid slot and restarts the SoC.
    unsafe {
        let err = esp_ota_mark_app_invalid_rollback_and_reboot();
        warn!("ota: rollback returned unexpectedly err={err}; restarting");
        esp_restart();
    }
}

/// Returns `true` if a valid ELF coredump is stored in the `coredump` flash partition.
pub fn has_flash_coredump() -> bool {
    // SAFETY: thread-safe ESP-IDF flash coredump check.
    unsafe { esp_core_dump_image_check() == ESP_OK }
}

/// Read the raw ELF coredump bytes from flash, if one is present.
fn read_flash_coredump() -> Option<Vec<u8>> {
    // SAFETY: queries coredump address/size and reads from the `coredump` data partition.
    unsafe {
        if esp_core_dump_image_check() != ESP_OK {
            return None;
        }
        let mut addr: usize = 0;
        let mut size: usize = 0;
        if esp_core_dump_image_get(&mut addr, &mut size) != ESP_OK || size == 0 || size > 65_536 {
            return None;
        }
        let part = esp_partition_find_first(
            esp_partition_type_t_ESP_PARTITION_TYPE_DATA,
            esp_partition_subtype_t_ESP_PARTITION_SUBTYPE_DATA_COREDUMP,
            core::ptr::null(),
        );
        if part.is_null() {
            return None;
        }
        let part_addr = (*part).address as usize;
        let rel_offset = addr.saturating_sub(part_addr);
        let mut buf = vec![0u8; size];
        if esp_partition_read(part, rel_offset, buf.as_mut_ptr().cast(), size) != ESP_OK {
            return None;
        }
        Some(buf)
    }
}

/// Erase any stored flash coredump after it has been uploaded.
fn erase_flash_coredump() {
    // SAFETY: thread-safe ESP-IDF flash coredump erase.
    unsafe {
        let err = esp_core_dump_image_erase();
        if err == ESP_OK {
            info!("coredump: erased flash coredump partition");
        } else {
            warn!("coredump: erase failed err={err}");
        }
    }
}

struct OtaWriterState {
    expected_chip_id: u16,
    min_ota_battery_mv: u16,
    handle: Option<esp_ota_handle_t>,
    partition: *const esp_partition_t,
    expected_size: u32,
    expected_sha256: String,
    compression: OtaCompression,
    /// Uncompressed firmware bytes written to flash and hashed.
    written: u32,
    /// Wire payload bytes accepted so far (equals `written` when uncompressed).
    wire_written: u32,
    /// First 14 uncompressed bytes buffered for `esp_image_header_t` validation.
    header_buf: [u8; 14],
    header_len: usize,
    deflate: Option<OtaDeflateDecoder>,
    next_notify_at: u32,
    last_activity_us: u64,
    last_gap_notify_us: u64,
    hasher: Sha256,
    reboot_pending: bool,
}

// SAFETY: `partition` points to an immutable ESP-IDF partition descriptor table entry in flash/ROM.
unsafe impl Send for OtaWriterState {}

impl OtaWriterState {
    fn new(expected_chip_id: u16, min_ota_battery_mv: u16) -> Self {
        Self {
            expected_chip_id,
            min_ota_battery_mv,
            handle: None,
            partition: core::ptr::null(),
            expected_size: 0,
            expected_sha256: String::new(),
            compression: OtaCompression::None,
            written: 0,
            wire_written: 0,
            header_buf: [0u8; 14],
            header_len: 0,
            deflate: None,
            next_notify_at: 0,
            last_activity_us: 0,
            last_gap_notify_us: 0,
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
        self.compression = OtaCompression::None;
        self.written = 0;
        self.wire_written = 0;
        self.header_len = 0;
        self.deflate = None;
        self.next_notify_at = 0;
        self.last_gap_notify_us = 0;
        self.hasher = Sha256::new();
    }

    fn begin(
        &mut self,
        size: u32,
        sha256: String,
        compression: OtaCompression,
        battery_mv: u16,
    ) -> OtaStatus {
        self.last_activity_us = now_us();
        self.last_gap_notify_us = 0;
        if self.min_ota_battery_mv > 0 && battery_mv > 0 && battery_mv < self.min_ota_battery_mv {
            return OtaStatus::Error {
                message: format!(
                    "battery too low for OTA: {battery_mv}mV < {}mV",
                    self.min_ota_battery_mv
                ),
            };
        }
        if size == 0 || size > OTA_SLOT_BYTES {
            return OtaStatus::Error {
                message: format!("invalid size {size}"),
            };
        }
        // Resumable OTA: if an in-progress session matches `(size, sha256, compression)` and
        // already has bytes written, resume from `self.wire_written` without re-erasing flash.
        if self.handle.is_some()
            && self.expected_size == size
            && self.expected_sha256 == sha256
            && self.compression == compression
            && self.wire_written > 0
            && self.written <= size
        {
            info!(
                "ota: resuming in-progress session at wire offset {} (written {}/{size})",
                self.wire_written, self.written
            );
            return OtaStatus::Ready {
                total: size,
                offset: self.wire_written,
            };
        }

        self.abort_active();
        // SAFETY: queries ESP-IDF's partition table for the inactive OTA app slot and opens it.
        unsafe {
            let part = esp_ota_get_next_update_partition(core::ptr::null());
            if part.is_null() {
                return OtaStatus::Error {
                    message: "no inactive OTA slot (run make flash-all)".to_string(),
                };
            }
            let mut handle: esp_ota_handle_t = 0;
            // Erase sectors incrementally on each `esp_ota_write` (~30 ms/sector) instead of
            // blocking the NimBLE host task for 3+ seconds erasing the full slot upfront.
            let err = esp_ota_begin(part, OTA_WITH_SEQUENTIAL_WRITES as usize, &mut handle);
            if err != ESP_OK {
                return OtaStatus::Error {
                    message: format!("esp_ota_begin err={err}"),
                };
            }
            self.handle = Some(handle);
            self.partition = part;
            self.expected_size = size;
            self.expected_sha256 = sha256;
            self.compression = compression;
            self.written = 0;
            self.wire_written = 0;
            self.header_len = 0;
            self.deflate = (compression == OtaCompression::Deflate).then(OtaDeflateDecoder::new);
            self.next_notify_at = 16 * 1024;
            self.hasher = Sha256::new();
            info!("ota: opened inactive partition for {size} bytes (compression={compression:?})");
            OtaStatus::Ready {
                total: size,
                offset: 0,
            }
        }
    }

    /// Validate header (on the first 14 bytes), write uncompressed firmware bytes to flash,
    /// and feed them into the running SHA-256 hasher.
    fn write_plain_bytes(&mut self, handle: esp_ota_handle_t, plain: &[u8]) -> Result<(), String> {
        if plain.is_empty() {
            return Ok(());
        }
        if self.header_len < self.header_buf.len() {
            let take = (self.header_buf.len() - self.header_len).min(plain.len());
            self.header_buf[self.header_len..self.header_len + take]
                .copy_from_slice(&plain[..take]);
            self.header_len += take;
            validate_esp_image_header(&self.header_buf[..self.header_len], self.expected_chip_id)?;
        }
        let next_written = self.written.saturating_add(plain.len() as u32);
        if next_written > self.expected_size {
            return Err(format!("overflow: {next_written} > {}", self.expected_size));
        }
        // SAFETY: `handle` is an active OTA handle and `plain` is valid for `plain.len()` bytes.
        let err = unsafe { esp_ota_write(handle, plain.as_ptr().cast(), plain.len()) };
        if err != ESP_OK {
            return Err(format!("esp_ota_write err={err}"));
        }
        self.hasher.update(plain);
        self.written = next_written;
        Ok(())
    }

    fn write_chunk(&mut self, raw: &[u8]) -> Option<OtaStatus> {
        let now = now_us();
        self.last_activity_us = now;
        let Some(handle) = self.handle else {
            return Some(OtaStatus::Error {
                message: "write before BEGIN".to_string(),
            });
        };
        if raw.is_empty() {
            return None;
        }

        // Decode framed `(offset, crc32, payload)` chunk if present; otherwise accept legacy raw chunk.
        let chunk: &[u8] = match decode_ota_chunk_frame(raw) {
            Ok(Some(frame)) => {
                if frame.offset < self.wire_written {
                    // Duplicate/retransmitted chunk already written; ignore cleanly.
                    return None;
                }
                if frame.offset > self.wire_written {
                    if now.saturating_sub(self.last_gap_notify_us) >= 300_000 {
                        self.last_gap_notify_us = now;
                        warn!(
                            "ota: chunk gap got={} expected={}, requesting resume",
                            frame.offset, self.wire_written
                        );
                        return Some(OtaStatus::Ready {
                            total: self.expected_size,
                            offset: self.wire_written,
                        });
                    }
                    return None;
                }
                frame.payload
            }
            Ok(None) => raw,
            Err(msg) => {
                return Some(OtaStatus::Error { message: msg });
            }
        };

        if chunk.is_empty() {
            return None;
        }

        let write_result = if let Some(mut decoder) = self.deflate.take() {
            let res = decoder.push(chunk, |plain| self.write_plain_bytes(handle, plain));
            self.deflate = Some(decoder);
            res
        } else {
            self.write_plain_bytes(handle, chunk)
        };

        if let Err(message) = write_result {
            self.abort_active();
            return Some(OtaStatus::Error { message });
        }

        self.wire_written = self.wire_written.saturating_add(chunk.len() as u32);
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
        if let Some(mut decoder) = self.deflate.take() {
            if let Err(message) = decoder.finish(|plain| self.write_plain_bytes(handle, plain)) {
                // SAFETY: `handle` was just taken and is still open.
                unsafe {
                    let _ = esp_ota_abort(handle);
                }
                self.abort_active();
                return OtaStatus::Error { message };
            }
        }
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

/// Persistent NimBLE peripheral + OTA / Profile / Coredump / App-Command GATT server initialized once per boot.
pub struct BleOtaNode {
    board: BoardSpec,
    connected: Arc<AtomicBool>,
    last_battery_mv: Arc<AtomicU16>,
    ota_state: Arc<Mutex<OtaWriterState>>,
    profile_char: Option<ProfileCharHandle>,
    pending_cmd: Arc<Mutex<Option<AppCommandRequest>>>,
    app_cmd_char: Arc<esp32_nimble::utilities::mutex::Mutex<BLECharacteristic>>,
}

impl BleOtaNode {
    /// Initialize NimBLE and register the OTA + Profile + Coredump + App-Command GATT service once.
    pub fn init(board: BoardSpec) -> Self {
        let device = BLEDevice::take();
        let _ = device.set_preferred_mtu(512);
        let server = device.get_server();

        let connected = Arc::new(AtomicBool::new(false));
        let last_battery_mv = Arc::new(AtomicU16::new(0));
        let ota_state = Arc::new(Mutex::new(OtaWriterState::new(
            board.chip_id,
            board.min_ota_battery_mv,
        )));
        let pending_cmd: Arc<Mutex<Option<AppCommandRequest>>> = Arc::new(Mutex::new(None));

        let conn_on_connect = Arc::clone(&connected);
        let state_on_connect = Arc::clone(&ota_state);
        server.on_connect(move |server, desc| {
            lock_or_recover(&state_on_connect).last_activity_us = now_us();
            conn_on_connect.store(true, Ordering::SeqCst);
            info!("ble connected for OTA/profile/coredump: {desc:?}");
            // Fast 7.5 ms - 15 ms connection interval for high-throughput BLE OTA streaming,
            // with a 6 s supervision timeout (600 * 10 ms) to tolerate flash sector erases.
            let _ = server.update_conn_params(desc.conn_handle(), 6, 12, 0, 600);
        });

        let conn_on_disconnect = Arc::clone(&connected);
        server.on_disconnect(move |_desc, reason| {
            // Keep any in-progress OTA session open across transient disconnects so the
            // client can reconnect and resume from `written` via `BEGIN <size> <sha256>`.
            info!("ble disconnected: {reason:?}");
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

        // Coredump GATT characteristic: READ/NOTIFY streams flash ELF in `MC` chunks; WRITE `CLEAR` erases it.
        let coredump_char = service.lock().create_characteristic(
            uuid_or_panic(COREDUMP_CHAR_UUID),
            NimbleProperties::READ | NimbleProperties::NOTIFY | NimbleProperties::WRITE,
        );
        if has_flash_coredump() {
            coredump_char.lock().set_value(b"AVAILABLE");
        } else {
            coredump_char.lock().set_value(b"NONE");
        }
        let cd_char_sub = Arc::clone(&coredump_char);
        coredump_char
            .lock()
            .on_subscribe(move |_ch, _desc, sub_value| {
                if sub_value.is_empty() {
                    return;
                }
                if let Some(elf_bytes) = read_flash_coredump() {
                    info!(
                        "coredump: streaming {} bytes over BLE GATT",
                        elf_bytes.len()
                    );
                    for frame in encode_blob_frames(&elf_bytes, COREDUMP_CHUNK_PAYLOAD) {
                        cd_char_sub.lock().set_value(&frame).notify();
                        FreeRtos::delay_ms(5);
                    }
                }
            });
        let cd_char_wr = Arc::clone(&coredump_char);
        coredump_char.lock().on_write(move |args| {
            let cmd = String::from_utf8_lossy(args.recv_data());
            if cmd.trim().eq_ignore_ascii_case("CLEAR") {
                erase_flash_coredump();
                cd_char_wr.lock().set_value(b"NONE");
            }
        });

        // Declarative app command characteristic: WRITE `<id>` or `<id> <count>`; READ/NOTIFY status.
        let app_cmd_char = service.lock().create_characteristic(
            uuid_or_panic(APP_COMMAND_CHAR_UUID),
            NimbleProperties::READ | NimbleProperties::NOTIFY | NimbleProperties::WRITE,
        );
        app_cmd_char.lock().set_value(b"IDLE");
        let cmd_queue_wr = Arc::clone(&pending_cmd);
        let cmd_char_wr = Arc::clone(&app_cmd_char);
        let cmd_state_wr = Arc::clone(&ota_state);
        app_cmd_char.lock().on_write(move |args| {
            let raw = String::from_utf8_lossy(args.recv_data());
            lock_or_recover(&cmd_state_wr).last_activity_us = now_us();
            let reply = match parse_app_command(raw.as_ref()) {
                Some(req) => {
                    let msg = format!("QUEUED {} {}", req.id, req.count);
                    info!("app command queued: {} x{}", req.id, req.count);
                    *lock_or_recover(&cmd_queue_wr) = Some(req);
                    msg
                }
                None => {
                    warn!("app command rejected: {raw:?}");
                    "ERR invalid app command".to_string()
                }
            };
            cmd_char_wr.lock().set_value(reply.as_bytes()).notify();
        });

        let ctrl_state = Arc::clone(&ota_state);
        let ctrl_status_char = Arc::clone(&status_char);
        let ctrl_batt = Arc::clone(&last_battery_mv);
        control_char.lock().on_write(move |args| {
            let raw = String::from_utf8_lossy(args.recv_data());
            info!("ota control write: {raw}");
            let mut guard = lock_or_recover(&ctrl_state);
            let batt = ctrl_batt.load(Ordering::Relaxed);
            let reply = match parse_ota_command(raw.as_ref()) {
                Some(OtaCommand::Begin {
                    size,
                    sha256,
                    compression,
                }) => guard.begin(size, sha256, compression, batt),
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
            let mut guard = lock_or_recover(&data_state);
            if let Some(status) = guard.write_chunk(chunk) {
                notify_ota_status(&data_status_char, &status);
            }
        });

        Self {
            board,
            connected,
            last_battery_mv,
            ota_state,
            profile_char,
            pending_cmd,
            app_cmd_char,
        }
    }

    /// Take the most recently queued app command (if any) after the BLE burst has stopped.
    pub fn take_pending_command(&self) -> Option<AppCommandRequest> {
        lock_or_recover(&self.pending_cmd).take()
    }

    /// Update the readable status on `APP_COMMAND_CHAR_UUID` (e.g. `"RUNNING run 3/10"` or `"IDLE"`).
    pub fn set_app_command_status(&self, status: &str) {
        self.app_cmd_char.lock().set_value(status.as_bytes());
    }

    /// Broadcast `metrics` inside BLE Manufacturer Specific Data (`0xFFFF`) for `burst_ms`.
    /// If an iPhone connects during that window to pull the WakeProfile/coredump or push an
    /// OTA image, stay awake (feeding the Task Watchdog) until the session finishes or times out.
    pub fn broadcast_burst(&self, metrics: &AdvMetrics, profile_json: Option<&str>, burst_ms: u32) {
        self.last_battery_mv
            .store(metrics.battery_mv, Ordering::Relaxed);
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
            info!("ota: iPhone connected during burst; holding awake for BLE session");
            let mut waited_ms: u32 = 0;
            while self.connected.load(Ordering::SeqCst) && waited_ms < OTA_SESSION_TIMEOUT_MS {
                FreeRtos::delay_ms(50);
                // SAFETY: resets the current task's TWDT timer while holding awake for BLE OTA.
                unsafe {
                    let _ = esp_task_wdt_reset();
                }
                waited_ms = waited_ms.saturating_add(50);
                let guard = lock_or_recover(&self.ota_state);
                if guard.reboot_pending {
                    drop(guard);
                    // Give NimBLE 250 ms to flush the final `OK sha256=...` notification before rebooting.
                    FreeRtos::delay_ms(250);
                    unsafe {
                        esp_restart();
                    }
                }
                if now_us().saturating_sub(guard.last_activity_us) > OTA_IDLE_TIMEOUT_US {
                    warn!("ota: idle timeout on BLE connection; closing wait loop");
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
        COREDUMP_CHAR_UUID => uuid128!("1a3c0003-36e1-4688-b7f5-ea07361bc303"),
        APP_COMMAND_CHAR_UUID => uuid128!("1a3c0004-36e1-4688-b7f5-ea07361bc303"),
        other => panic!("unknown UUID {other}"),
    }
}
