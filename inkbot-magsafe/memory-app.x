/* nRF52833 production application slot with S113 7.3.0.
 *
 * S113 occupies 112 KiB of flash. Replace this conservative 32 KiB RAM
 * reservation with the value that the SoftDevice reports during enable for
 * the released GATT, L2CAP, MTU, data-length, and connection configuration.
 *
 * Flash above the 176 KiB primary slot is reserved for a 180 KiB update slot,
 * an 8 KiB settings journal, a 32 KiB signed bootloader, and a 4 KiB state page:
 *
 *   0x00000..0x1C000  MBR and S113
 *   0x1C000..0x48000  primary application
 *   0x48000..0x75000  update candidate
 *   0x75000..0x77000  settings journal
 *   0x77000..0x7F000  bootloader
 *   0x7F000..0x80000  boot and monotonic-version state
 *
 * The bootloader implementation must validate these provisional sizes before
 * production release.
 */
MEMORY
{
  FLASH : ORIGIN = 0x0001C000,       LENGTH = 176K
  RAM   : ORIGIN = 0x20000000 + 32K, LENGTH = 128K - 32K
}
