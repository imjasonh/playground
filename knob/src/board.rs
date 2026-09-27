//! Pin map for the Waveshare ESP32-S3-Knob-Touch-LCD-1.8.
//!
//! Display, touch, encoder, haptics, battery, microphone, and SDMMC pins
//! match the Waveshare schematic and the public hardware-explorer sketch.
//! The UART and the jack do not. The schematic names S3 TX/RX
//! `ESP32S3_TX`/`ESP32S3_RX` on GPIO38/GPIO48, and companion TX/RX on
//! GPIO23/GPIO18. The PCM5100A mute (`XSMT`) is companion GPIO32. The
//! companion I2S trio is BCK GPIO25, DIN GPIO26, WS GPIO27. GPIO0 is
//! `I2S_SWITCH_IN`. See `docs/hardware.md`.

/// Round panel width in pixels.
pub const PANEL_W: u16 = 360;

/// Round panel height in pixels.
pub const PANEL_H: u16 = 360;

/// Inactive-slot size on the S3, in bytes. A BLE image larger than this is rejected.
pub const APP_SLOT_S3: u32 = 0x0060_0000;

/// Inactive-slot size on the companion ESP32, in bytes.
pub const APP_SLOT_ESP32: u32 = 0x0018_0000;

/// UART baud between the two MCUs. The factory images use 921600 8N1.
pub const LINK_BAUD: u32 = 921_600;

/// Classic Bluetooth name advertised by the companion. Phones pair here for A2DP.
pub const CLASSIC_BT_NAME: &str = "Playground Knob Audio";

/// ESP32-S3R8, the chip that owns the panel.
pub mod s3 {
    /// I2C SDA. CST816 touch and DRV2605 share this bus.
    pub const I2C_SDA: i32 = 11;
    /// I2C SCL.
    pub const I2C_SCL: i32 = 12;
    /// CST816 7-bit address.
    pub const TOUCH_ADDR: u8 = 0x15;
    /// CST816 interrupt. The driver also polls, so a missing edge still updates.
    pub const TOUCH_INT: i32 = 9;
    /// CST816 reset, active low.
    pub const TOUCH_RST: i32 = 10;
    /// DRV2605 7-bit address. The motor is an LRA.
    pub const HAPTIC_ADDR: u8 = 0x5A;

    /// Knob pulse for one direction. A falling edge while ENCODER_B is high is one step.
    pub const ENCODER_A: i32 = 8;
    /// Knob pulse for the other direction. A falling edge while ENCODER_A is high is one step.
    pub const ENCODER_B: i32 = 7;

    /// ST77916 chip select.
    pub const LCD_CS: i32 = 14;
    /// ST77916 QSPI clock.
    pub const LCD_PCLK: i32 = 13;
    /// ST77916 QSPI data 0.
    pub const LCD_D0: i32 = 15;
    /// ST77916 QSPI data 1.
    pub const LCD_D1: i32 = 16;
    /// ST77916 QSPI data 2.
    pub const LCD_D2: i32 = 17;
    /// ST77916 QSPI data 3.
    pub const LCD_D3: i32 = 18;
    /// ST77916 reset, active low.
    pub const LCD_RST: i32 = 21;
    /// Backlight LED, PWM.
    pub const LCD_BL: i32 = 47;

    /// Battery divider ADC. Multiply the pin voltage by 2.
    pub const BATTERY_ADC: i32 = 1;

    /// CH445P `I2S_SWITCH_IN`. High selects this chip's I2S trio
    /// (GPIO39, GPIO40, GPIO41). Low selects the companion trio.
    /// Strap pin, so the app drives it only after boot.
    pub const DAC_SWITCH: i32 = 0;

    /// PDM microphone clock. Strap pin GPIO45. Do not pull it at reset.
    pub const MIC_CLK: i32 = 45;
    /// PDM microphone data. Strap pin GPIO46.
    pub const MIC_DATA: i32 = 46;

    /// SDMMC clock.
    pub const SD_CLK: i32 = 4;
    /// SDMMC command. Strap pin GPIO3.
    pub const SD_CMD: i32 = 3;
    /// SDMMC data 0.
    pub const SD_D0: i32 = 5;
    /// SDMMC data 1.
    pub const SD_D1: i32 = 6;
    /// SDMMC data 2.
    pub const SD_D2: i32 = 42;
    /// SDMMC data 3.
    pub const SD_D3: i32 = 2;

    /// UART TX toward the companion ESP32. Schematic net `ESP32S3_TX`.
    pub const LINK_TX: i32 = 38;
    /// UART RX from the companion ESP32. Schematic net `ESP32S3_RX`.
    pub const LINK_RX: i32 = 48;

    /// PCM5100A bit clock on the S3 side of the CH445P. Not driven.
    /// GPIO0 low selects the companion trio instead.
    pub const I2S_BCLK: i32 = 39;
    /// PCM5100A word select on the S3 side of the switch.
    pub const I2S_WS: i32 = 40;
    /// PCM5100A data on the S3 side of the switch.
    pub const I2S_DOUT: i32 = 41;
}

/// ESP32-U4WDH. Classic Bluetooth, the second encoder, and the only I2S
/// master for the PCM5100A.
pub mod esp32 {
    /// UART TX toward the S3.
    pub const LINK_TX: i32 = 23;
    /// UART RX from the S3.
    pub const LINK_RX: i32 = 18;

    /// Second encoder channel A.
    pub const ENCODER_A: i32 = 19;
    /// Second encoder channel B.
    pub const ENCODER_B: i32 = 22;

    /// PCM5100A bit clock. Schematic net `ESP32_I2S_DAC_BCK`.
    pub const I2S_BCLK: i32 = 25;
    /// PCM5100A data. Schematic net `ESP32_I2S_DAC_DIN`.
    pub const I2S_DOUT: i32 = 26;
    /// PCM5100A word select. Schematic net `ESP32_I2S_DAC_LRCK/WS`.
    pub const I2S_WS: i32 = 27;
    /// PCM5100A XSMT. High unmutes. Low mutes.
    pub const DAC_UNMUTE: i32 = 32;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn s3_and_companion_link_pins_differ() {
        assert_ne!(s3::LINK_TX, esp32::LINK_TX);
        assert_ne!(s3::LINK_RX, esp32::LINK_RX);
        assert_eq!(LINK_BAUD, 921_600);
        assert_eq!(s3::LINK_TX, 38);
        assert_eq!(s3::LINK_RX, 48);
        assert_eq!(s3::I2S_BCLK, 39);
        assert_eq!(s3::I2S_WS, 40);
        assert_eq!(s3::I2S_DOUT, 41);
        assert_eq!(esp32::I2S_BCLK, 25);
        assert_eq!(esp32::I2S_DOUT, 26);
        assert_eq!(esp32::I2S_WS, 27);
        assert_eq!(esp32::DAC_UNMUTE, 32);
        assert_eq!(PANEL_W, 360);
    }

    #[test]
    fn slots_fit_the_partition_tables() {
        assert_eq!(APP_SLOT_S3, 0x600000);
        assert_eq!(APP_SLOT_ESP32, 0x180000);
    }
}
