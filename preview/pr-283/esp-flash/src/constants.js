/** ESP ROM image magic. Every bootloader and app image starts with this byte. */
export const ESP_IMAGE_MAGIC = 0xe9;

/** Bytes reserved for each OTA slot in inkbot-esp32 `partitions.csv`. */
export const OTA_SLOT_BYTES = 0x1f0000;

/** Flash offset of `ota_0`. */
export const OTA_0_OFFSET = 0x20000;

/** Flash offset of `ota_1`. */
export const OTA_1_OFFSET = 0x210000;

/** Default UART baud used to enter the ROM bootloader. */
export const ROM_BAUD = 115200;

/** Waveshare driver board flash geometry. */
export const FLASH_SIZE = "4MB";
export const FLASH_MODE = "dio";
export const FLASH_FREQ = "40m";

/** GHCR namespace that holds one package per firmware app. */
export const GHCR_NAMESPACE = "ghcr.io/imjasonh/playground";

export const OTA_APP_INKBOT = "inkbot-esp32";
export const OTA_APP_MAZE = "maze-esp32";
export const OTA_APPS = [OTA_APP_INKBOT, OTA_APP_MAZE];
export const OTA_TARGET_CHIP = "esp32";

/** OCI layer media type written by `inkbot-esp32/tools/publisher`. */
export const OTA_LAYER_MEDIA_TYPE = "application/vnd.esp32.firmware.bin";

/** OCI config media type written by `inkbot-esp32/tools/publisher`. */
export const OTA_CONFIG_MEDIA_TYPE = "application/vnd.esp32.firmware.v1+json";

/** Deployed cors-proxy Worker used to pull GHCR from GitHub Pages. */
export const DEFAULT_PROXY_BASE = "https://cors-proxy-worker.imjasonh.workers.dev";

export const DEFAULT_OTA_TAG = "latest";
