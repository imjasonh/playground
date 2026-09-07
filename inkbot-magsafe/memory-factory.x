/* Blank-device SWD image for one-time REGOUT0 provisioning.
 *
 * This image starts at the reset vector and must never be combined with S140.
 * Its flash range stops at the production application's 0x27000 origin so an
 * unexpectedly large factory image cannot consume application space.
 */
MEMORY
{
  FLASH : ORIGIN = 0x00000000, LENGTH = 156K
  RAM   : ORIGIN = 0x20000000, LENGTH = 128K
}
