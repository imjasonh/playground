/* The demo application: code in the application RAM region's instruction-bus
 * view, data in the part of the same region that the code doesn't alias, and
 * one read-only section in the flash data window so the bootloader's MMU
 * mapping gets exercised.
 */
MEMORY
{
  IRAM  : ORIGIN = 0x40380000, LENGTH = 0x8000
  DRAM  : ORIGIN = 0x3FC88000, LENGTH = 0x18000
  DROM  : ORIGIN = 0x3C000000, LENGTH = 0x10000
}

ENTRY(_start)

SECTIONS
{
  .text : ALIGN(4) { KEEP(*(.text._start)) *(.text .text.*) } > IRAM
  .flash_rodata : ALIGN(4) { KEEP(*(.flash_rodata)) } > DROM
  .rodata : ALIGN(4) { *(.srodata .srodata.*) *(.rodata .rodata.*) } > DRAM
  .data : ALIGN(4) { *(.sdata .sdata.*) *(.data .data.*) } > DRAM
  .bss (NOLOAD) : ALIGN(4) { _bss_start = .; *(.sbss .sbss.*) *(.bss .bss.*) *(COMMON) . = ALIGN(4); _bss_end = .; } > DRAM
  _stack_top = ORIGIN(DRAM) + LENGTH(DRAM);
  /DISCARD/ : { *(.eh_frame) *(.eh_frame_hdr) }
}
