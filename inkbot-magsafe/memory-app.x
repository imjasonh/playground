/* nRF52840 production application slot with S113 7.3.0.
 *
 * S113 occupies 112 KiB of flash. Replace this conservative 32 KiB RAM
 * reservation with the value that the SoftDevice reports during enable for
 * the released GATT, L2CAP, MTU, data-length, and connection configuration.
 *
 * The 1 MiB part leaves enough flash for equal 256 KiB application and update
 * slots, two complete frame slots, journals, and Nordic's boot metadata:
 *
 *   0x00000..0x1C000  MBR and S113
 *   0x1C000..0x5C000  primary application
 *   0x5C000..0x9C000  update candidate
 *   0x9C000..0xA0000  bond and settings journal
 *   0xA0000..0xAC000  committed-frame slot A
 *   0xAC000..0xB8000  committed-frame slot B
 *   0xB8000..0xBA000  frame metadata journal
 *   0xBA000..0xBC000  reset and fault journal
 *   0xBC000..0xE0000  reserved
 *   0xE0000..0xFE000  signed bootloader
 *   0xFE000..0xFF000  MBR parameter page
 *   0xFF000..0x100000 bootloader settings
 *
 * The released Nordic bootloader build and SoftDevice RAM report remain the
 * authority for the final boundaries.
 */
MEMORY
{
  FLASH : ORIGIN = 0x0001C000,       LENGTH = 256K
  RAM   : ORIGIN = 0x20000000 + 32K, LENGTH = 256K - 32K
}
