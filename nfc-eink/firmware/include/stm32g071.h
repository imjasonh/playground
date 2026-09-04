#ifndef NFC_EINK_STM32G071_H
#define NFC_EINK_STM32G071_H

#include <stdint.h>

#define PERIPH32(addr) (*(volatile uint32_t *)(uintptr_t)(addr))

#define RCC_BASE     0x40021000u
#define RCC_IOPENR   PERIPH32(RCC_BASE + 0x34)
#define RCC_APBENR1  PERIPH32(RCC_BASE + 0x3C)
#define RCC_APBENR2  PERIPH32(RCC_BASE + 0x40)
#define RCC_CCIPR    PERIPH32(RCC_BASE + 0x54)

#define GPIOA_BASE   0x50000000u
#define GPIOB_BASE   0x50000400u
#define GPIO_MODER(p)   PERIPH32((p) + 0x00)
#define GPIO_OTYPER(p)  PERIPH32((p) + 0x04)
#define GPIO_OSPEEDR(p) PERIPH32((p) + 0x08)
#define GPIO_PUPDR(p)   PERIPH32((p) + 0x0C)
#define GPIO_IDR(p)     PERIPH32((p) + 0x10)
#define GPIO_ODR(p)     PERIPH32((p) + 0x14)
#define GPIO_BSRR(p)    PERIPH32((p) + 0x18)
#define GPIO_AFRL(p)    PERIPH32((p) + 0x20)
#define GPIO_AFRH(p)    PERIPH32((p) + 0x24)

#define I2C1_BASE    0x40005400u
#define I2C_CR1(b)   PERIPH32((b) + 0x00)
#define I2C_CR2(b)   PERIPH32((b) + 0x04)
#define I2C_TIMINGR(b) PERIPH32((b) + 0x10)
#define I2C_ISR(b)   PERIPH32((b) + 0x18)
#define I2C_ICR(b)   PERIPH32((b) + 0x1C)
#define I2C_RXDR(b)  PERIPH32((b) + 0x24)
#define I2C_TXDR(b)  PERIPH32((b) + 0x28)

#define SPI1_BASE    0x40013000u
#define SPI_CR1(b)   PERIPH32((b) + 0x00)
#define SPI_CR2(b)   PERIPH32((b) + 0x04)
#define SPI_SR(b)    PERIPH32((b) + 0x08)
#define SPI_DR(b)    PERIPH32((b) + 0x0C)

#define USART2_BASE  0x40004400u
#define USART_CR1(b) PERIPH32((b) + 0x00)
#define USART_BRR(b) PERIPH32((b) + 0x0C)
#define USART_ISR(b) PERIPH32((b) + 0x1C)
#define USART_TDR(b) PERIPH32((b) + 0x28)

#define ADC_BASE     0x40012400u
#define ADC_ISR      PERIPH32(ADC_BASE + 0x00)
#define ADC_CR       PERIPH32(ADC_BASE + 0x08)
#define ADC_CFGR1    PERIPH32(ADC_BASE + 0x0C)
#define ADC_SMPR     PERIPH32(ADC_BASE + 0x14)
#define ADC_CHSELR   PERIPH32(ADC_BASE + 0x28)
#define ADC_DR       PERIPH32(ADC_BASE + 0x40)
#define ADC_CCR      PERIPH32(0x40012708u)

#define FLASH_ACR    PERIPH32(0x40022000u)

#endif
