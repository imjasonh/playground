/-
Blinks the LED on GPIO8 of an ESP32-C3. GPIO8 drives the LED on the common
"ESP32-C3 SuperMini" boards. Espressif's ESP32-C3-DevKitM-1 has an addressable
RGB LED on GPIO8 instead, which this program can't drive.

Register addresses are from the ESP32-C3 Technical Reference Manual. Not yet
tested on hardware.
-/
import VerifiedFw.Examples.Counter

namespace VerifiedFw.Examples.Blinky

open VerifiedFw.RiscV VerifiedFw.Lang VerifiedFw.Examples

def set (addr val : Word) : Stmt := .store addr (.const val)

/-- The key that unlocks watchdog configuration registers. -/
def wdtKey : Word := 0x50D83AA1

/-- In flash boot, the ROM leaves the RTC watchdog, the super watchdog, and the
timer group 0 watchdog running. Each would reset the chip within seconds. -/
def disableWatchdogs : Stmt := seqs [
  -- RTC watchdog: unlock RTC_CNTL_WDTWPROTECT, clear RTC_CNTL_WDTCONFIG0, lock.
  set 0x600080A8 wdtKey, set 0x60008090 0, set 0x600080A8 0,
  -- Super watchdog: unlock RTC_CNTL_SWD_WPROTECT, set SWD_AUTO_FEED_EN (bit 31).
  set 0x600080B0 0x8F1D312A, set 0x600080AC 0x80000000, set 0x600080B0 0,
  -- Timer group 0 and 1 watchdogs: unlock TIMG_WDTWPROTECT, clear
  -- TIMG_WDTCONFIG0 with TIMG_WDT_CONF_UPDATE_EN (bit 22) set, lock.
  set 0x6001F064 wdtKey, set 0x6001F048 0x00400000, set 0x6001F064 0,
  set 0x60020064 wdtKey, set 0x60020048 0x00400000, set 0x60020064 0]

def ledBit : Word := 1 <<< 8

/-- Routes GPIO8 to the GPIO output register and enables its driver. -/
def setupLed : Stmt := seqs [
  -- IO_MUX_GPIO8_REG: function 1 (GPIO), drive strength 2.
  set 0x60009024 0x1800,
  -- GPIO_FUNC8_OUT_SEL_CFG_REG: signal 128, the plain GPIO output.
  set 0x60004574 0x80,
  -- GPIO_ENABLE_W1TS_REG.
  set 0x60004024 ledBit]

/-- GPIO_OUT_W1TS_REG and GPIO_OUT_W1TC_REG. The SuperMini's LED lights when
the pin is low. -/
def ledOn : Stmt := set 0x6000400C ledBit
def ledOff : Stmt := set 0x60004008 ledBit

/-- About half a second at the ROM's CPU clock. -/
def delay : Stmt := .loop 2000000 .skip

def blink : Stmt := seqs [ledOn, delay, ledOff, delay]

def blinks : Nat := 0xFFFFFFFF

def blinky : Program where
  globals := 0
  body := seqs [disableWatchdogs, setupLed, .loop blinks blink]

end VerifiedFw.Examples.Blinky
