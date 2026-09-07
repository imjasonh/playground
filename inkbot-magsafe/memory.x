/* nRF52833 with S140 7.3.0.
 *
 * S140 occupies 156 KiB of flash. This 31 KiB RAM reservation matches the
 * nrf-softdevice nRF52833 example and must be rechecked when the enabled GATT,
 * L2CAP, MTU, data-length, or connection counts change. The SoftDevice reports
 * the required application RAM origin during enable.
 */
MEMORY
{
  FLASH : ORIGIN = 0x00000000 + 156K, LENGTH = 512K - 156K
  RAM   : ORIGIN = 0x20000000 + 31K,  LENGTH = 128K - 31K
}
