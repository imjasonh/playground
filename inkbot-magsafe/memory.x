/* nRF52832 (xxAA): 512 KiB flash, 64 KiB RAM.
 *
 * This layout is for the SoftDevice-free bring-up build. When the S132
 * SoftDevice is added for BLE, move FLASH ORIGIN past the SoftDevice image
 * (about 0x26000 for S132 7.x) and raise RAM ORIGIN by the SoftDevice's RAM
 * reservation reported at sd_softdevice_enable, shrinking LENGTH to match.
 */
MEMORY
{
  FLASH : ORIGIN = 0x00000000, LENGTH = 512K
  RAM   : ORIGIN = 0x20000000, LENGTH = 64K
}
