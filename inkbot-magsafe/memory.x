/* nRF52833 production application slot with S140 7.3.0.
 *
 * S140 occupies 156 KiB of flash. This 31 KiB RAM reservation matches the
 * nrf-softdevice nRF52833 example and must be rechecked when the enabled GATT,
 * L2CAP, MTU, data-length, or connection counts change. The SoftDevice reports
 * the required application RAM origin during enable.
 *
 * Flash above the 160 KiB primary slot is reserved for a same-size update
 * slot, a 32 KiB signed bootloader, and one 4 KiB state page:
 *
 *   0x00000..0x27000  MBR and S140
 *   0x27000..0x4F000  primary application
 *   0x4F000..0x77000  update candidate
 *   0x77000..0x7F000  bootloader
 *   0x7F000..0x80000  boot and monotonic-version state
 *
 * The bootloader implementation must validate these provisional sizes before
 * production release.
 */
MEMORY
{
  FLASH : ORIGIN = 0x00027000,       LENGTH = 160K
  RAM   : ORIGIN = 0x20000000 + 31K,  LENGTH = 128K - 31K
}
