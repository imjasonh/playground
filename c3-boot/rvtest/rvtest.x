/* The lockstep test firmware, which the ROM loads as if it were the
 * bootloader: code in the bootloader's instruction region, data in its data
 * region, and the test buffer at the start of the application RAM region,
 * the fixed address that the generated cases name. (hardware)
 */
MEMORY
{
  IRAM : ORIGIN = 0x403A0000, LENGTH = 0x24000
  DRAM : ORIGIN = 0x3FCC4000, LENGTH = 0x18710
  BUF  : ORIGIN = 0x3FC80000, LENGTH = 0x100
}

ENTRY(_start)

SECTIONS
{
  .text : ALIGN(4) { KEEP(*(.text._start)) *(.text .text.*) } > IRAM
  .rodata : ALIGN(4) { *(.srodata .srodata.*) *(.rodata .rodata.*) } > DRAM
  .data : ALIGN(4) { *(.sdata .sdata.*) *(.data .data.*) } > DRAM
  .bss (NOLOAD) : ALIGN(4) { _bss_start = .; *(.sbss .sbss.*) *(.bss .bss.*) *(COMMON) . = ALIGN(4); _bss_end = .; } > DRAM
  .rvbuf (NOLOAD) : { KEEP(*(.rvbuf)) } > BUF
  _stack_top = ORIGIN(DRAM) + LENGTH(DRAM);
  /DISCARD/ : { *(.eh_frame) *(.eh_frame_hdr) }
}
