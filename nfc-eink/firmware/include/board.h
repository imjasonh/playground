#ifndef NFC_EINK_BOARD_H
#define NFC_EINK_BOARD_H

/* STM32G071CBT6 LQFP48. Nets match the schematic. */

#define GPIO_PORTA 0
#define GPIO_PORTB 1

#define PIN_VSTORE_DIV 0  /* PA0 ADC */
#define PIN_DBG_TX     2  /* PA2 */
#define PIN_DBG_RX     3  /* PA3 */
#define PIN_EPD_CS     4  /* PA4 */
#define PIN_EPD_SCK    5  /* PA5 */
#define PIN_EPD_BUSY   6  /* PA6 */
#define PIN_EPD_MOSI   7  /* PA7 */
#define PIN_EPD_DC     8  /* PA8 */
#define PIN_SWDIO     13  /* PA13 */
#define PIN_SWCLK     14  /* PA14 */
#define PIN_EPD_RST   15  /* PA15 */

#define PIN_EPD_PWR_EN 0  /* PB0 */
#define PIN_NFC_FD     5  /* PB5 */
#define PIN_I2C_SCL    6  /* PB6 */
#define PIN_I2C_SDA    7  /* PB7 */

#define NTAG_I2C_ADDR  0x55
#define NTAG_SRAM_BLK  0xF8
#define NTAG_SESS_BLK  0xFE
#define NTAG_CFG_2K    0xE8

/*
 * VSTORE divider is 220k/100k. ADC uses VDD (~3.29 V) as VREF.
 * 780 counts is about 2.0 V on the tank, above the TPS61023 1.8 V
 * rising UVLO with a little margin for the Schottky.
 */
#define VSTORE_READY_COUNTS 780
#define VSTORE_WAIT_MS 2000

#define NTAG_FIRST_CHUNK_SPINS 4000
#define NTAG_NEXT_CHUNK_SPINS 1500

#endif
