# 7.5-inch e-ink SSH client

The `eink/` firmware is a single-purpose SSH display client. It has no local
shell: ESP-IDF firmware connects to WiFi, opens one authenticated SSH session,
requests an 80×25 PTY, types a configured command, renders the output, closes
the TCP connection, and puts the panel into deep sleep.

## Hardware

- Waveshare e-Paper ESP32 Driver Board, SKU 15823 / Amazon B07M5CNP3B.
- Waveshare 7.5-inch raw monochrome 800×480 panel, SKU 13187 / Amazon
  B075R69T93.
- USB data cable and a 5 V USB supply.

The raw panel connects through the board's 24-pin ZIF connector or its included
FFC extension and adapter. There is no separate Raspberry Pi HAT and no GPIO
wiring.

The driver board fixes the signals to:

| Signal | ESP32 GPIO |
|---|---:|
| SCLK | 13 |
| MOSI | 14 |
| CS | 15 |
| DC | 27 |
| RST | 26 |
| BUSY | 25 |

The firmware currently targets the modern monochrome 800×480 V2/UC8179
initialization sequence, refreshes the complete panel, then deep-sleeps it.
Partial refresh remains disabled until the delivered panel's exact revision is
confirmed on hardware.

Before powering the display, check the driver board's resistor-selection
switch. The 7.5-inch panel needs the 0.47 Ω RESE path; current boards label that
position `B`, while some old schematics reverse the letter. Prefer the resistor
value printed on the board over the letter.

Record these markings when the hardware arrives:

- driver-board revision and ESP32 module text;
- switch labels and any `0.47R` / `3R` markings;
- panel rear sticker (`075BN-T7`, suffix, and V2/date);
- flex-tail text (`FPC-C001`, `WFT0583CZ61`, or `WF0583CZ09`).

## Provisioning

Create the local configuration:

```bash
make provisioning.toml
```

Add WiFi and Sigstore settings as described in [`ota.md`](ota.md), then add:

```toml
[ssh]
host = "server.example.com"
port = 22
username = "jason"
host_key = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAA..."
command = "uptime; uname -a"
```

Obtain the server key with:

```bash
ssh-keyscan -t ed25519 server.example.com | awk '{print $2, $3}'
```

`ssh-keyscan` does not authenticate what it retrieves. Compare the key or
fingerprint through another trusted channel before provisioning it. The
provisioner validates the OpenSSH encoding and stores only the 32-byte Ed25519
key. Firmware rejects any different key or key algorithm.

Flash and monitor:

```bash
make APP=eink bootstrap
make APP=eink monitor
```

## First-boot key enrollment

After WiFi starts, the device generates an Ed25519 key and stores its 32-byte
seed in NVS. The complete public key is printed to USB serial:

```text
ssh-ed25519 AAAA... esp32-eink
```

Append that line to the target account's `~/.ssh/authorized_keys`, then reset
the ESP32. The next boot authenticates, requests an `xterm` PTY with 80 columns
and 25 rows, types the configured command followed by `exit`, and displays the
captured output.

The private seed is plaintext in NVS for this prototype. `make provision` writes
a complete NVS image and therefore replaces a generated key; after
re-provisioning, enroll the newly generated public key again. Production
hardening would add NVS/flash encryption and Secure Boot.

## Display model

One monochrome framebuffer costs 48,000 bytes. Text uses the built-in 9×18
monospace font with 19-pixel line spacing and 40-pixel horizontal margins:
80 columns × 25 rows fit in 800×480 while remaining physically readable.

The SSH handshake and session run on a dedicated 32 KiB worker stack, which is
joined before allocating the framebuffer. The signed-OTA thread starts only
after the panel refresh. This deliberately prevents the SSH packet buffers,
display framebuffer, and OTA/TLS stack from occupying RAM at the same time.

The terminal parser handles printable ASCII, CR/LF, tabs, backspace, basic
cursor movement, line/screen clearing, and ignores color attributes. It is
intentionally not a complete xterm implementation yet.

## OTA

The e-ink image polls `ghcr.io/imjasonh/esp32-eink:latest`. The playground
publish workflow signs each artifact keylessly, and the device verifies the
Sigstore certificate chain, signer identity, DSSE signature, and artifact
digest before writing the inactive OTA slot.

An OTA image is marked valid only after both WiFi and a full display refresh
succeed. A failed display bring-up reboots into the previous slot.
