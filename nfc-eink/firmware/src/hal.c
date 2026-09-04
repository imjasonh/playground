#include "hal.h"

#include "board.h"
#include "stm32g071.h"

static uint32_t port_base(int port)
{
    return port == GPIO_PORTB ? GPIOB_BASE : GPIOA_BASE;
}

static void gpio_mode(int port, int pin, int mode, int af, int open_drain)
{
    uint32_t base = port_base(port);
    uint32_t moder = GPIO_MODER(base);
    uint32_t afr;

    moder &= ~(3u << (pin * 2));
    moder |= ((uint32_t)mode << (pin * 2));
    GPIO_MODER(base) = moder;
    if (open_drain) {
        GPIO_OTYPER(base) |= (1u << pin);
    } else {
        GPIO_OTYPER(base) &= ~(1u << pin);
    }
    if (pin < 8) {
        afr = GPIO_AFRL(base);
        afr &= ~(15u << (pin * 4));
        afr |= ((uint32_t)af << (pin * 4));
        GPIO_AFRL(base) = afr;
    } else {
        afr = GPIO_AFRH(base);
        afr &= ~(15u << ((pin - 8) * 4));
        afr |= ((uint32_t)af << ((pin - 8) * 4));
        GPIO_AFRH(base) = afr;
    }
}

void gpio_out(int port, int pin, int val)
{
    uint32_t base = port_base(port);
    if (val) {
        GPIO_BSRR(base) = (1u << pin);
    } else {
        GPIO_BSRR(base) = (1u << (pin + 16));
    }
}

int gpio_in(int port, int pin)
{
    return (GPIO_IDR(port_base(port)) >> pin) & 1u;
}

void hal_delay_ms(uint32_t ms)
{
    /* 16 MHz HSI. Each inner iter is a nop plus the volatile count. */
    while (ms--) {
        volatile uint32_t n = 4000;
        while (n--) {
            __asm volatile ("nop");
        }
        iwdg_kick();
    }
}

void iwdg_kick(void)
{
    IWDG_KR = 0xAAAAu;
}

void epd_rail(int on)
{
    gpio_out(GPIO_PORTB, PIN_EPD_PWR_EN, on);
}

void mcu_wfi(void)
{
    __asm volatile ("wfi");
}

static void clocks(void)
{
    FLASH_ACR = (FLASH_ACR & ~0x7u) | 0x1u;
    RCC_IOPENR |= (1u << 0) | (1u << 1); /* GPIOA, GPIOB */
    RCC_APBENR1 |= (1u << 21) | (1u << 17); /* I2C1, USART2 */
    RCC_APBENR2 |= (1u << 12) | (1u << 20); /* SPI1, ADC */
}

static void gpio_setup(void)
{
    gpio_mode(GPIO_PORTA, PIN_EPD_CS, 1, 0, 0);
    gpio_mode(GPIO_PORTA, PIN_EPD_DC, 1, 0, 0);
    gpio_mode(GPIO_PORTA, PIN_EPD_RST, 1, 0, 0);
    gpio_mode(GPIO_PORTA, PIN_EPD_BUSY, 0, 0, 0);
    gpio_mode(GPIO_PORTA, PIN_EPD_SCK, 2, 0, 0);  /* AF0 SPI1 */
    gpio_mode(GPIO_PORTA, PIN_EPD_MOSI, 2, 0, 0);
    gpio_mode(GPIO_PORTA, PIN_DBG_TX, 2, 1, 0);   /* AF1 USART2 */
    gpio_mode(GPIO_PORTA, PIN_DBG_RX, 2, 1, 0);
    gpio_mode(GPIO_PORTA, PIN_VSTORE_DIV, 3, 0, 0); /* analog */
    gpio_mode(GPIO_PORTB, PIN_EPD_PWR_EN, 1, 0, 0);
    gpio_mode(GPIO_PORTB, PIN_NFC_FD, 0, 0, 0);
    GPIO_PUPDR(GPIOB_BASE) |= (1u << (PIN_NFC_FD * 2)); /* pull-up */
    gpio_mode(GPIO_PORTB, PIN_I2C_SCL, 2, 6, 1); /* AF6 I2C1 OD */
    gpio_mode(GPIO_PORTB, PIN_I2C_SDA, 2, 6, 1);
    gpio_out(GPIO_PORTA, PIN_EPD_CS, 1);
    gpio_out(GPIO_PORTA, PIN_EPD_DC, 0);
    /* Hold RST low while +3V3_EPD is off so the pin cannot back-power VCI. */
    gpio_out(GPIO_PORTA, PIN_EPD_RST, 0);
    gpio_out(GPIO_PORTB, PIN_EPD_PWR_EN, 0);
}

static void spi_setup(void)
{
    /* Master, SSI/SSM, BR = /8 (2 MHz at 16 MHz), SPE */
    SPI_CR1(SPI1_BASE) = (1u << 2) | (1u << 6) | (1u << 8) | (1u << 9) | (2u << 3);
    SPI_CR2(SPI1_BASE) = (7u << 8); /* 8-bit */
}

static void i2c_setup(void)
{
    I2C_CR1(I2C1_BASE) = 0;
    /* 100 kHz @ 16 MHz. RM0444 timing examples. */
    I2C_TIMINGR(I2C1_BASE) = 0x00303D5Bu;
    I2C_CR1(I2C1_BASE) = 1u;
}

static void uart_setup(void)
{
    USART_BRR(USART2_BASE) = 16000000u / 115200u;
    USART_CR1(USART2_BASE) = (1u << 0) | (1u << 3);
}

static void adc_setup(void)
{
    ADC_CR = 0;
    ADC_CFGR1 = 0;
    ADC_SMPR = 7u;
    ADC_CHSELR = (1u << 0); /* IN0 = PA0 */
    ADC_CR |= (1u << 28); /* ADVREGEN */
    hal_delay_ms(1);
    ADC_CR |= (1u << 31); /* ADCAL */
    while (ADC_CR & (1u << 31)) {
    }
    ADC_ISR = 1u;
    ADC_CR |= (1u << 0); /* ADEN */
    while ((ADC_ISR & 1u) == 0) {
    }
}

static void iwdg_setup(void)
{
    RCC_CSR |= 1u; /* LSION */
    while ((RCC_CSR & 2u) == 0) {
    }
    IWDG_KR = 0x5555u;
    IWDG_PR = 6u;     /* /256 */
    IWDG_RLR = 1023u; /* about 8 s at 32 kHz LSI */
    IWDG_KR = 0xCCCCu;
}

void hal_init(void)
{
    clocks();
    gpio_setup();
    spi_setup();
    i2c_setup();
    uart_setup();
    adc_setup();
    iwdg_setup();
}

void spi_tx(const uint8_t *data, uint32_t n)
{
    uint32_t i;
    for (i = 0; i < n; i++) {
        while ((SPI_SR(SPI1_BASE) & (1u << 1)) == 0) {
        }
        SPI_DR(SPI1_BASE) = data[i];
        while ((SPI_SR(SPI1_BASE) & (1u << 0)) == 0) {
        }
        (void)SPI_DR(SPI1_BASE);
    }
}

static int i2c_wait(uint32_t mask, uint32_t timeout)
{
    while (timeout--) {
        if (I2C_ISR(I2C1_BASE) & mask) {
            return 0;
        }
        if (I2C_ISR(I2C1_BASE) & (1u << 4)) {
            I2C_ICR(I2C1_BASE) = (1u << 4);
            return -1;
        }
    }
    return -2;
}

void i2c_recover(void)
{
    I2C_CR1(I2C1_BASE) = 0;
    I2C_ICR(I2C1_BASE) = 0x3F38u;
    I2C_CR1(I2C1_BASE) = 1u;
}

int i2c_write(uint8_t addr7, const uint8_t *data, uint32_t n)
{
    uint32_t i;

    /* START + AUTOEND so NBYTES also emits STOP. Wait for STOPF (bit 5). */
    I2C_CR2(I2C1_BASE) = ((uint32_t)addr7 << 1) | (n << 16) | (1u << 13) | (1u << 25);
    for (i = 0; i < n; i++) {
        if (i2c_wait(1u << 1, 80000) != 0) {
            return -1;
        }
        I2C_TXDR(I2C1_BASE) = data[i];
    }
    if (i2c_wait(1u << 5, 80000) != 0) {
        return -2;
    }
    I2C_ICR(I2C1_BASE) = (1u << 5);
    return 0;
}

int i2c_read(uint8_t addr7, uint8_t *data, uint32_t n)
{
    uint32_t i;

    I2C_CR2(I2C1_BASE) = ((uint32_t)addr7 << 1) | (n << 16) | (1u << 10) | (1u << 13) | (1u << 25);
    for (i = 0; i < n; i++) {
        if (i2c_wait(1u << 2, 80000) != 0) {
            return -1;
        }
        data[i] = (uint8_t)I2C_RXDR(I2C1_BASE);
    }
    if (i2c_wait(1u << 5, 80000) != 0) {
        return -2;
    }
    I2C_ICR(I2C1_BASE) = (1u << 5);
    return 0;
}

uint16_t adc_vstore_div(void)
{
    ADC_CR |= (1u << 2); /* ADSTART */
    while ((ADC_ISR & 1u) == 0) {
    }
    ADC_ISR = 1u;
    return (uint16_t)ADC_DR;
}

void uart_write(const char *s)
{
    while (*s) {
        while ((USART_ISR(USART2_BASE) & (1u << 7)) == 0) {
        }
        USART_TDR(USART2_BASE) = (uint8_t)*s++;
    }
}
