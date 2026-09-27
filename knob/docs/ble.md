# BLE contract

The S3 advertises as `PlaygroundKnob`. One service. The iOS app that
does not exist yet must use these UUIDs.

| Characteristic | UUID | Properties |
|----------------|------|------------|
| Service | `7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1001` | |
| Info | `7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1002` | Read |
| Text | `7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1003` | Read, write, notify |
| Status | `7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1004` | Read, notify |
| OTA control | `7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1005` | Write |
| OTA data | `7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1006` | Write, write without response |
| OTA status | `7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1007` | Read, notify |
| HID consumer | `7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1008` | Read, notify |

Preferred MTU is 256. OTA payloads must stay at or under 240 bytes plus
the 2-byte sequence.

## Text

UTF-8, one command per write. The verb is case-insensitive. The notify
is the reply, except `status`, which is already on the status characteristic.

| Write | Reply |
|-------|--------|
| `ping` | `pong` |
| `apps` | Comma-separated ids compiled into this image |
| `open clock` | `open clock`, or `missing clock` |
| `reboot s3` | The S3 restarts |
| `reboot esp32` | `reboot esp32`, then the companion restarts |
| `wifi <ssid> <pass>` | `wifi saved`. One token each, 32 and 64 characters max. |

Status, about once a second:

```
fw=knob-s3/0.1 app=dial up=4 bat=3900 link=up bt=on
```

`link` is `up` when a UART frame arrived in the last 3 seconds. `bt` is
the companion's Classic Bluetooth state: `off`, `pair`, `wait`, or `on`.

## Info

`KNOB`, version byte `1`, firmware-id length, firmware id, max chunk as
`u16` little-endian, slot limit as `u32` little-endian. The id in this
blob is `knob-s3/0.1`. The companion id, `knob-esp32/0.1`, is not
advertised. The iOS app learns which image it is sending from the OTA
target byte.

## OTA

Control opcodes:

| Byte | Meaning | Payload |
|------|---------|---------|
| `0x01` | Begin | target `u8`, size `u32` le, CRC-32 `u32` le |
| `0x02` | Abort | none |
| `0x03` | Finish | none |
| `0x04` | Reboot the target from the last begin | none |
| `0x05` | Mark the running S3 slot valid | none |

Target `0` is the S3. Target `1` is the companion. CRC-32 covers the raw
image bytes in order.

Data writes are `seq` as `u16` little-endian, starting at 0, then the
bytes. Sequence gaps fail the session.

Status notifies are 7 bytes. State (`0` idle, `1` receiving, `2`
complete, `3` failed), target (`0xFF` when idle), bytes written as `u32`
little-endian, then an error code. `0` means no error. Other codes are
listed in `src/ota.rs`.

A companion image is not written to the S3 slot. Each accepted chunk is
framed on the UART and written to the companion's inactive slot. Finish
checks the CRC on the S3 before the companion is told to activate. Reboot
is a separate opcode, so a failed finish does not reset the chip.
