/* nRF52833 (xxAA): 512 KiB flash, 128 KiB RAM.
 *
 * SoftDevice-free layout for the scaffold. When the S132 (or S140) SoftDevice
 * is added for BLE, move FLASH ORIGIN past the SoftDevice image (about 0x27000
 * for S140 7.x) and raise RAM ORIGIN by the SoftDevice's RAM requirement. The
 * 48 KiB mono framebuffer plus the SoftDevice fit comfortably in 128 KiB.
 */
MEMORY
{
  FLASH : ORIGIN = 0x00000000, LENGTH = 512K
  RAM   : ORIGIN = 0x20000000, LENGTH = 128K
}
