#include "epd.h"

#include "board.h"
#include "hal.h"

static void epd_cmd(uint8_t c)
{
    gpio_out(GPIO_PORTA, PIN_EPD_CS, 0);
    gpio_out(GPIO_PORTA, PIN_EPD_DC, 0);
    spi_tx(&c, 1);
    gpio_out(GPIO_PORTA, PIN_EPD_CS, 1);
}

static void epd_data(const uint8_t *d, uint32_t n)
{
    gpio_out(GPIO_PORTA, PIN_EPD_CS, 0);
    gpio_out(GPIO_PORTA, PIN_EPD_DC, 1);
    spi_tx(d, n);
    gpio_out(GPIO_PORTA, PIN_EPD_CS, 1);
}

static void epd_data1(uint8_t b)
{
    epd_data(&b, 1);
}

static void epd_wait(uint32_t timeout_ms)
{
    while (timeout_ms--) {
        if (gpio_in(GPIO_PORTA, PIN_EPD_BUSY) == 0) {
            return;
        }
        hal_delay_ms(1);
    }
}

void epd_hw_reset(void)
{
    gpio_out(GPIO_PORTA, PIN_EPD_RST, 0);
    hal_delay_ms(10);
    gpio_out(GPIO_PORTA, PIN_EPD_RST, 1);
    hal_delay_ms(10);
}

void epd_init(void)
{
    uint8_t mux[3] = {0x2B, 0x01, 0x00};

    epd_hw_reset();
    epd_cmd(0x12);
    hal_delay_ms(10);
    epd_cmd(0x01);
    epd_data(mux, 3);
    epd_cmd(0x3C);
    epd_data1(0x01);
    epd_cmd(0x18);
    epd_data1(0x80);
    epd_cmd(0x11);
    epd_data1(0x03);
    epd_cmd(0x44);
    epd_data1(0x00);
    epd_data1(0x31);
    epd_cmd(0x45);
    epd_data1(0x00);
    epd_data1(0x00);
    epd_data1(0x2B);
    epd_data1(0x01);
}

void epd_write_frame(const uint8_t frame[FRAME_BYTES])
{
    epd_cmd(0x4E);
    epd_data1(0x00);
    epd_cmd(0x4F);
    epd_data1(0x00);
    epd_data1(0x00);
    epd_cmd(0x24);
    epd_data(frame, FRAME_BYTES);
    epd_cmd(0x4E);
    epd_data1(0x00);
    epd_cmd(0x4F);
    epd_data1(0x00);
    epd_data1(0x00);
    epd_cmd(0x26);
    epd_data(frame, FRAME_BYTES);
}

void epd_refresh(void)
{
    uint8_t ctl[2] = {0x40, 0x00};

    epd_cmd(0x21);
    epd_data(ctl, 2);
    epd_cmd(0x22);
    epd_data1(0xF7);
    epd_cmd(0x20);
    epd_wait(8000);
}

void epd_sleep(void)
{
    epd_cmd(0x10);
    epd_data1(0x01);
}
