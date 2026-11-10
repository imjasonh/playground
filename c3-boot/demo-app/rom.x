/* ESP32-C3 ROM functions the bootloader calls, from ESP-IDF's
 * esp32c3.rom.ld. (hardware) */
PROVIDE(ets_printf = 0x40000040);
PROVIDE(esp_rom_spiflash_erase_sector = 0x40000128);
PROVIDE(esp_rom_spiflash_write = 0x4000012c);
PROVIDE(esp_rom_spiflash_read = 0x40000130);
PROVIDE(esp_rom_spiflash_unlock = 0x40000140);
PROVIDE(Cache_Invalidate_ICache_All = 0x400004d8);
PROVIDE(Cache_Suspend_ICache = 0x40000524);
PROVIDE(Cache_Resume_ICache = 0x40000528);
