//! Shared multi-MCU protocol, maze renderer, BLE GATT OTA, and wake profiler library.

pub mod maze;
pub mod panel;
pub mod protocol;

#[cfg(feature = "firmware")]
pub mod apps;
#[cfg(feature = "firmware")]
pub mod ble_ota;
#[cfg(feature = "firmware")]
pub mod boards;
#[cfg(feature = "firmware")]
pub mod epd_display;
#[cfg(feature = "firmware")]
pub mod platform;
#[cfg(feature = "firmware")]
pub mod profiler;

pub use protocol::{
    crc32, decode_adv_packet, decode_blob_frame, decode_board_id, decode_mfg_data,
    decode_ota_chunk_frame, encode_adv_packet, encode_blob_frames, encode_board_flags,
    encode_mfg_data, encode_ota_chunk_frame, encode_ota_command, format_ota_status,
    format_otlp_json, format_status_line, format_wake_profile_json, is_esp_code_addr,
    parse_ota_command, parse_ota_status, parse_status_line, reset_reason_name, simulate_epd_frame,
    simulate_sensor_filter, validate_esp_image_header, AdvMetrics, BlobReassembler, BoardSpec,
    OtaChunkFrame, OtaCommand, OtaStatus, PcHistogram, PcSample, PhaseAccumulator, ProfileSpan,
    RtcState, SpanRecorder, WakeProfile, ADV_PACKET_LEN, BASE_FIRMWARE_ID, BLOB_FRAME_HEADER_LEN,
    BLOB_FRAME_MAGIC, BOARD_WAVESHARE_EPD75, BOARD_XIAO_ESP32C3, CHIP_ID_ESP32, CHIP_ID_ESP32C3,
    COMPANY_ID, COREDUMP_CHAR_UUID, DEVICE_NAME, EPD_FRAME_BYTES, EPD_FULL_REFRESH_SIM_US,
    EPD_HEIGHT, EPD_PARTIAL_REFRESH_SIM_US, EPD_WIDTH, FIRMWARE_ID, FLAG_BROWNOUT_RESET,
    FLAG_DEEP_SLEEP_WAKE, FLAG_EPD_ATTACHED, FLAG_EPD_PARTIAL, MAX_CRASH_STREAK, MFG_DATA_LEN,
    OTA_CHUNK_HEADER_LEN, OTA_CHUNK_MAGIC, OTA_CONTROL_UUID, OTA_DATA_UUID, OTA_SERVICE_UUID,
    OTA_SLOT_BYTES, OTA_STATUS_UUID, PAYLOAD_LEN, PROFILE_CHAR_UUID, PROTOCOL_VERSION,
    RTC_STATE_MAGIC,
};
