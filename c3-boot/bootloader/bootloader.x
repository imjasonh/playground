/* Memory layout for the c3-boot bootloader, from c3-boot/docs/formats.md.
 *
 * The bootloader owns data-bus addresses 0x3FCA0000 through 0x3FCDC710.
 * Code runs from the instruction-bus alias of the lower part of that region,
 * and data and the stack use the data-bus view of the upper part, so the two
 * never alias each other. (hardware)
 */
MEMORY
{
  IRAM : ORIGIN = 0x403A0000, LENGTH = 0x24000
  DRAM : ORIGIN = 0x3FCC4000, LENGTH = 0x18710
}

ENTRY(_start)

SECTIONS
{
  .text : ALIGN(4)
  {
    KEEP(*(.text._start))
    *(.text .text.*)
  } > IRAM

  .rodata : ALIGN(4)
  {
    *(.srodata .srodata.*)
    *(.rodata .rodata.*)
  } > DRAM

  .data : ALIGN(4)
  {
    *(.sdata .sdata.*)
    *(.data .data.*)
  } > DRAM

  .bss (NOLOAD) : ALIGN(4)
  {
    _bss_start = .;
    *(.sbss .sbss.*)
    *(.bss .bss.*)
    *(COMMON)
    . = ALIGN(4);
    _bss_end = .;
  } > DRAM

  .stack (NOLOAD) : ALIGN(16)
  {
    _stack_bottom = .;
    . = ORIGIN(DRAM) + LENGTH(DRAM);
    _stack_top = .;
  } > DRAM

  ASSERT(_stack_top - _stack_bottom >= 0xC000, "bootloader stack is under 48 KiB")

  /DISCARD/ : { *(.eh_frame) *(.eh_frame_hdr) }
}
