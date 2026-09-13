//! Host-testable pieces of the Playground BLE firmware.
//!
//! Device GATT / GPIO code lives in `main.rs` (feature `firmware`).

pub mod protocol;

pub use protocol::{
    encode_command, format_status, parse_command, parse_status, Command, DeviceState, Status,
    COMMAND_UUID, DEVICE_NAME, FIRMWARE_ID, MAX_BLINK_MS, MIN_BLINK_MS, SERVICE_UUID, STATUS_UUID,
};
