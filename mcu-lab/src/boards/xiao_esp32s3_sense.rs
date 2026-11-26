//! Seeed Studio XIAO ESP32-S3 Sense board support package.
//!
//! Hardware pinout (official Seeed Studio XIAO ESP32-S3 Sense schematic):
//! - Camera DVP (OV2640 / OV3660 / OV5640):
//!   - `XCLK`: GPIO10, `SIOD` (SDA): GPIO40, `SIOC` (SCL): GPIO39
//!   - `Y9`: GPIO48, `Y8`: GPIO11, `Y7`: GPIO12, `Y6`: GPIO14
//!   - `Y5`: GPIO16, `Y4`: GPIO18, `Y3`: GPIO17, `Y2`: GPIO15
//!   - `VSYNC`: GPIO38, `HREF`: GPIO47, `PCLK`: GPIO13
//! - Digital PDM Microphone (MSM261D3526H1CPM):
//!   - `CLK`: GPIO42, `DATA`: GPIO41
//! - MicroSD Card (SPI):
//!   - `SCK`: GPIO7 (D8), `MISO`: GPIO8 (D9), `MOSI`: GPIO9 (D10), `CS`: GPIO21

use std::ffi::CStr;

use anyhow::{anyhow, Result};
use esp_idf_svc::eventloop::EspSystemEventLoop;
use esp_idf_svc::fs::fatfs::Fatfs;
use esp_idf_svc::hal::gpio::AnyIOPin;
use esp_idf_svc::hal::i2s::config::{
    Config as I2sConfig, DataBitWidth, PdmRxClkConfig, PdmRxConfig, PdmRxGpioConfig,
    PdmRxSlotConfig, SlotMode,
};
use esp_idf_svc::hal::i2s::{I2sDriver, I2sRx, I2S0};
use esp_idf_svc::hal::modem::Modem;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::hal::sd::spi::SdSpiHostDriver;
use esp_idf_svc::hal::sd::{SdCardConfiguration, SdCardDriver};
use esp_idf_svc::hal::spi::config::DriverConfig;
use esp_idf_svc::hal::spi::{SpiDriver, SPI2};
use esp_idf_svc::io::vfs::MountedFatfs;
use esp_idf_svc::nvs::EspDefaultNvsPartition;
use esp_idf_svc::sys::camera::{
    camera_config_t, camera_config_t__bindgen_ty_1, camera_config_t__bindgen_ty_2,
    camera_fb_location_t_CAMERA_FB_IN_PSRAM, camera_fb_t, camera_grab_mode_t_CAMERA_GRAB_LATEST,
    esp_camera_deinit, esp_camera_fb_get, esp_camera_fb_return, esp_camera_init,
    framesize_t_FRAMESIZE_VGA, ledc_channel_t_LEDC_CHANNEL_0, ledc_timer_t_LEDC_TIMER_0,
    pixformat_t_PIXFORMAT_JPEG,
};
use esp_idf_svc::sys::{esp_vfs_fat_info, ESP_OK};
use esp_idf_svc::wifi::{
    AccessPointConfiguration, AuthMethod, BlockingWifi, ClientConfiguration, Configuration, EspWifi,
};
use log::{info, warn};

use crate::boards::{Board, HasSenseAV};
use crate::platform::RunMode;
use crate::protocol::{BoardSpec, BOARD_XIAO_ESP32S3_SENSE, CHIP_ID_ESP32S3};
use crate::sense_clip::{DEFAULT_AUDIO_SAMPLE_RATE, DEFAULT_SOFTAP_IP, DEFAULT_SOFTAP_SSID};

/// Nominal USB rail voltage reported in `battery_mv` (5.0 V USB-C powered board).
const USB_RAIL_MV: u16 = 5000;

/// Mount point for the onboard microSD card FAT32 filesystem.
pub const SD_MOUNT_POINT: &str = "/sdcard";

/// Directory on the microSD card where recorded `.mov` clips are stored.
pub const CLIPS_DIR: &str = "/sdcard/clips";

/// Uninitialized peripheral bundle handed to [`RecorderApp`](crate::apps::recorder::RecorderApp)
/// so `xiao-esp32s3-sense-base` can boot and accept BLE OTA even without an SD card or camera.
pub struct SenseHardware {
    pub modem: Modem<'static>,
    pub spi2: SPI2<'static>,
    pub sd_sck: AnyIOPin<'static>,
    pub sd_miso: AnyIOPin<'static>,
    pub sd_mosi: AnyIOPin<'static>,
    pub sd_cs: AnyIOPin<'static>,
    pub i2s0: I2S0<'static>,
    pub mic_clk: AnyIOPin<'static>,
    pub mic_data: AnyIOPin<'static>,
}

/// Seeed Studio XIAO ESP32-S3 Sense (Xtensa LX7 dual-core 240 MHz, 8 MB Flash, 8 MB Octal PSRAM).
pub struct XiaoEsp32S3Sense {
    hardware: Option<SenseHardware>,
}

impl Board for XiaoEsp32S3Sense {
    const SPEC: BoardSpec = BoardSpec {
        board_id: BOARD_XIAO_ESP32S3_SENSE,
        board: "xiao-esp32s3-sense",
        chip: "esp32s3",
        gap_name: "XIAO-S3",
        chip_id: CHIP_ID_ESP32S3,
        cpu_mhz: 240,
        min_ota_battery_mv: 0,
    };

    fn default_run_mode() -> RunMode {
        RunMode::Continuous {
            burst_ms: 500,
            min_step_ms: 5_500,
        }
    }

    fn init(peripherals: Peripherals) -> Result<Self> {
        let hardware = SenseHardware {
            modem: peripherals.modem,
            spi2: peripherals.spi2,
            sd_sck: peripherals.pins.gpio7.into(),
            sd_miso: peripherals.pins.gpio8.into(),
            sd_mosi: peripherals.pins.gpio9.into(),
            sd_cs: peripherals.pins.gpio21.into(),
            i2s0: peripherals.i2s0,
            mic_clk: peripherals.pins.gpio42.into(),
            mic_data: peripherals.pins.gpio41.into(),
        };
        Ok(Self {
            hardware: Some(hardware),
        })
    }

    fn read_battery_mv(&mut self) -> u16 {
        USB_RAIL_MV
    }
}

impl HasSenseAV for XiaoEsp32S3Sense {
    fn take_sense_hardware(&mut self) -> Result<SenseHardware> {
        self.hardware
            .take()
            .ok_or_else(|| anyhow!("XIAO ESP32-S3 Sense hardware already taken"))
    }
}

/// Active Wi-Fi network info for status reporting and BLE `WakeProfile` discovery.
#[derive(Debug, Clone)]
pub struct SenseWifiInfo {
    pub mode: String,
    pub ssid: String,
    pub ip: String,
}

/// Owns the initialized Wi-Fi driver for the lifetime of the recorder app.
pub struct SenseWifi {
    _wifi: BlockingWifi<EspWifi<'static>>,
    pub info: SenseWifiInfo,
}

impl SenseWifi {
    /// Connect to `MCU_LAB_WIFI_SSID` (if set at build time) or start the default
    /// `XIAO-S3-Sense` SoftAP (`192.168.4.1`) so the iOS app can connect directly.
    pub fn start(modem: Modem<'static>) -> Result<Self> {
        let sys_loop = EspSystemEventLoop::take()?;
        let nvs = EspDefaultNvsPartition::take()?;
        let mut wifi =
            BlockingWifi::wrap(EspWifi::new(modem, sys_loop.clone(), Some(nvs))?, sys_loop)?;

        if let Some(ssid) = option_env!("MCU_LAB_WIFI_SSID").filter(|s| !s.is_empty()) {
            let pass = option_env!("MCU_LAB_WIFI_PASS").unwrap_or("");
            info!("sense-wifi: connecting to STA SSID={ssid}");
            let auth = if pass.is_empty() {
                AuthMethod::None
            } else {
                AuthMethod::WPA2Personal
            };
            let cfg = Configuration::Client(ClientConfiguration {
                ssid: ssid
                    .try_into()
                    .map_err(|_| anyhow!("Wi-Fi SSID too long"))?,
                password: pass
                    .try_into()
                    .map_err(|_| anyhow!("Wi-Fi password too long"))?,
                auth_method: auth,
                ..Default::default()
            });
            if wifi.set_configuration(&cfg).is_ok()
                && wifi.start().is_ok()
                && wifi.connect().is_ok()
                && wifi.wait_netif_up().is_ok()
            {
                let ip = wifi
                    .wifi()
                    .sta_netif()
                    .get_ip_info()
                    .map(|info| info.ip.to_string())
                    .unwrap_or_else(|_| "0.0.0.0".to_string());
                info!("sense-wifi: STA connected ip={ip}");
                return Ok(Self {
                    _wifi: wifi,
                    info: SenseWifiInfo {
                        mode: "sta".to_string(),
                        ssid: ssid.to_string(),
                        ip,
                    },
                });
            }
            warn!("sense-wifi: STA connect failed; falling back to SoftAP {DEFAULT_SOFTAP_SSID}");
            let _ = wifi.stop();
        }

        let ap_cfg = Configuration::AccessPoint(AccessPointConfiguration {
            ssid: DEFAULT_SOFTAP_SSID
                .try_into()
                .map_err(|_| anyhow!("SoftAP SSID too long"))?,
            auth_method: AuthMethod::None,
            max_connections: 4,
            channel: 6,
            ..Default::default()
        });
        wifi.set_configuration(&ap_cfg)?;
        wifi.start()?;
        wifi.wait_netif_up()?;
        let ip = wifi
            .wifi()
            .ap_netif()
            .get_ip_info()
            .map(|info| info.ip.to_string())
            .unwrap_or_else(|_| DEFAULT_SOFTAP_IP.to_string());
        info!("sense-wifi: SoftAP started ssid={DEFAULT_SOFTAP_SSID} ip={ip}");
        Ok(Self {
            _wifi: wifi,
            info: SenseWifiInfo {
                mode: "ap".to_string(),
                ssid: DEFAULT_SOFTAP_SSID.to_string(),
                ip,
            },
        })
    }
}

/// Mounted microSD FAT32 filesystem at `/sdcard`.
pub struct SenseSdCard {
    _mounted: MountedFatfs<Fatfs<SdCardDriver<SdSpiHostDriver<'static, SpiDriver<'static>>>>>,
}

impl SenseSdCard {
    /// Initialize SPI2 and mount the onboard microSD card at `/sdcard`.
    pub fn mount(
        spi2: SPI2<'static>,
        sck: AnyIOPin<'static>,
        miso: AnyIOPin<'static>,
        mosi: AnyIOPin<'static>,
        cs: AnyIOPin<'static>,
    ) -> Result<Self> {
        let spi_driver = SpiDriver::new(spi2, sck, mosi, Some(miso), &DriverConfig::new())?;
        let sd_host = SdSpiHostDriver::new(
            spi_driver,
            Some(cs),
            Option::<AnyIOPin<'static>>::None,
            Option::<AnyIOPin<'static>>::None,
            Option::<AnyIOPin<'static>>::None,
            None,
        )?;
        let sd_card = SdCardDriver::new_spi(sd_host, &SdCardConfiguration::new())?;
        let fatfs = Fatfs::new_sdcard(0, sd_card)?;
        let mounted = MountedFatfs::mount(fatfs, SD_MOUNT_POINT, 8)?;
        std::fs::create_dir_all(CLIPS_DIR)?;
        info!("sense-sd: mounted microSD at {SD_MOUNT_POINT}");
        Ok(Self { _mounted: mounted })
    }

    /// Return `(total_bytes, free_bytes)` for the mounted `/sdcard` FAT32 volume.
    pub fn space_info(&self) -> Result<(u64, u64)> {
        sd_space_info()
    }
}

/// Query `(total_bytes, free_bytes)` for the mounted `/sdcard` FAT32 volume.
pub fn sd_space_info() -> Result<(u64, u64)> {
    let mut total: u64 = 0;
    let mut free: u64 = 0;
    let mount_cstr = CStr::from_bytes_with_nul(b"/sdcard\0")?;
    // SAFETY: `mount_cstr` is NUL-terminated and `total`/`free` are valid out pointers.
    let err = unsafe { esp_vfs_fat_info(mount_cstr.as_ptr(), &mut total, &mut free) };
    if err != ESP_OK {
        return Err(anyhow!("esp_vfs_fat_info failed: err={err}"));
    }
    Ok((total, free))
}

/// Borrowed camera frame buffer that automatically returns to `esp32-camera` on drop.
pub struct CameraFrame {
    fb: *mut camera_fb_t,
}

impl CameraFrame {
    pub fn bytes(&self) -> &[u8] {
        // SAFETY: `fb` is non-null and valid until `esp_camera_fb_return` in `Drop`.
        unsafe { core::slice::from_raw_parts((*self.fb).buf, (*self.fb).len) }
    }

    pub fn width(&self) -> u16 {
        // SAFETY: `fb` is non-null.
        unsafe { (*self.fb).width as u16 }
    }

    pub fn height(&self) -> u16 {
        // SAFETY: `fb` is non-null.
        unsafe { (*self.fb).height as u16 }
    }
}

impl Drop for CameraFrame {
    fn drop(&mut self) {
        if !self.fb.is_null() {
            // SAFETY: returns frame buffer previously acquired by `esp_camera_fb_get`.
            unsafe {
                esp_camera_fb_return(self.fb);
            }
        }
    }
}

/// DVP camera driver for the XIAO ESP32-S3 Sense expansion board (OV2640 / OV3660 / OV5640).
pub struct SenseCamera {
    _private: (),
}

impl SenseCamera {
    pub fn init() -> Result<Self> {
        // SAFETY: zero-initializing C config struct before populating all required fields.
        let mut cfg: camera_config_t = unsafe { core::mem::zeroed() };
        cfg.pin_pwdn = -1;
        cfg.pin_reset = -1;
        cfg.pin_xclk = 10;
        cfg.__bindgen_anon_1 = camera_config_t__bindgen_ty_1 { pin_sccb_sda: 40 };
        cfg.__bindgen_anon_2 = camera_config_t__bindgen_ty_2 { pin_sccb_scl: 39 };
        cfg.pin_d7 = 48;
        cfg.pin_d6 = 11;
        cfg.pin_d5 = 12;
        cfg.pin_d4 = 14;
        cfg.pin_d3 = 16;
        cfg.pin_d2 = 18;
        cfg.pin_d1 = 17;
        cfg.pin_d0 = 15;
        cfg.pin_vsync = 38;
        cfg.pin_href = 47;
        cfg.pin_pclk = 13;
        cfg.xclk_freq_hz = 20_000_000;
        cfg.ledc_timer = ledc_timer_t_LEDC_TIMER_0;
        cfg.ledc_channel = ledc_channel_t_LEDC_CHANNEL_0;
        cfg.pixel_format = pixformat_t_PIXFORMAT_JPEG;
        cfg.frame_size = framesize_t_FRAMESIZE_VGA;
        cfg.jpeg_quality = 14;
        cfg.fb_count = 2;
        cfg.fb_location = camera_fb_location_t_CAMERA_FB_IN_PSRAM;
        cfg.grab_mode = camera_grab_mode_t_CAMERA_GRAB_LATEST;
        cfg.sccb_i2c_port = 0;

        // SAFETY: `cfg` is initialized with valid XIAO ESP32-S3 Sense DVP pins.
        let err = unsafe { esp_camera_init(&cfg) };
        if err != ESP_OK {
            return Err(anyhow!("esp_camera_init failed: err={err:#x}"));
        }
        info!("sense-cam: initialized DVP JPEG camera (VGA, PSRAM)");
        Ok(Self { _private: () })
    }

    pub fn capture(&mut self) -> Option<CameraFrame> {
        // SAFETY: `esp_camera_init` succeeded; returns null on timeout/error.
        let fb = unsafe { esp_camera_fb_get() };
        if fb.is_null() {
            None
        } else {
            Some(CameraFrame { fb })
        }
    }
}

impl Drop for SenseCamera {
    fn drop(&mut self) {
        // SAFETY: matches `esp_camera_init` in `Self::init`.
        unsafe {
            let _ = esp_camera_deinit();
        }
    }
}

/// Onboard digital PDM microphone (16 kHz, 16-bit signed LE mono PCM on GPIO42/GPIO41).
pub struct SenseMic {
    driver: I2sDriver<'static, I2sRx>,
}

impl SenseMic {
    pub fn init(
        i2s0: I2S0<'static>,
        clk: AnyIOPin<'static>,
        data: AnyIOPin<'static>,
    ) -> Result<Self> {
        let pdm_cfg = PdmRxConfig::new(
            I2sConfig::default(),
            PdmRxClkConfig::from_sample_rate_hz(DEFAULT_AUDIO_SAMPLE_RATE),
            PdmRxSlotConfig::from_bits_per_sample_and_slot_mode(
                DataBitWidth::Bits16,
                SlotMode::Mono,
            ),
            PdmRxGpioConfig::new(false),
        );
        let mut driver = I2sDriver::new_pdm_rx(i2s0, &pdm_cfg, clk, data)?;
        driver.rx_enable()?;
        info!("sense-mic: initialized PDM RX ({DEFAULT_AUDIO_SAMPLE_RATE} Hz, 16-bit mono)");
        Ok(Self { driver })
    }

    /// Read available 16-bit LE PCM samples into `buf` with a short timeout (ms).
    pub fn read_pcm(&mut self, buf: &mut [u8], timeout_ticks: u32) -> usize {
        self.driver.read(buf, timeout_ticks).unwrap_or(0)
    }
}
