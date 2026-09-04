#ifndef NFC_EINK_HAL_H
#define NFC_EINK_HAL_H

#include <stdint.h>

void hal_init(void);
void hal_delay_ms(uint32_t ms);
void gpio_out(int port, int pin, int val);
int gpio_in(int port, int pin);
void spi_tx(const uint8_t *data, uint32_t n);
int i2c_write(uint8_t addr7, const uint8_t *data, uint32_t n);
int i2c_read(uint8_t addr7, uint8_t *data, uint32_t n);
void i2c_recover(void);
uint16_t adc_vstore_div(void);
void uart_write(const char *s);
void epd_rail(int on);
void iwdg_kick(void);
void mcu_wfi(void);

#endif
