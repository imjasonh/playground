//! Host-testable protocol and OTLP JSON formatter for `xiao-esp32c3`.
//!
//! Device BLE advertising, e-paper SPI benchmarking, and deep-sleep cycles live
//! in `main.rs` (feature `firmware`).

pub mod protocol;

pub use protocol::{
    decode_adv_packet, decode_metrics, decode_mfg_data, encode_adv_packet, encode_metrics,
    encode_mfg_data, format_otlp_json, format_status_line, parse_status_line, reset_reason_name,
    simulate_epd_frame, simulate_sensor_filter, AdvMetrics, PhaseAccumulator, ADV_PACKET_LEN,
    COMPANY_ID, DEVICE_NAME, EPD_FULL_REFRESH_SIM_US, EPD_HEIGHT, EPD_PARTIAL_REFRESH_SIM_US,
    EPD_WIDTH, FIRMWARE_ID, FLAG_BROWNOUT_RESET, FLAG_DEEP_SLEEP_WAKE, FLAG_EPD_ATTACHED,
    FLAG_EPD_PARTIAL, MFG_DATA_LEN, PAYLOAD_LEN, PROTOCOL_VERSION,
};
