#!/usr/bin/env python3
"""Records the ROM calls the c3-boot bootloader makes in QEMU.

Starts Espressif's QEMU halted with its GDB server, sets a breakpoint at
each ROM function the bootloader links against and at the bootloader's
`halt` function, and prints one line per stop, in the format
c3-boot-proofs' boot-sim prints:

- `call ADDRESS ARGS...` for a ROM call whose return address is in the
  bootloader, with the arguments it takes (the ROM's own calls to the same
  functions are skipped),
- `halt CODE` when the bootloader halts, and
- `jump ADDRESS A0` when it jumps to the application: when the bootloader
  logs "c3-boot: jumping to %x", a breakpoint goes on that address.

Usage: rsp-trace.py QEMU FLASH EFUSE HALT_ADDRESS
"""

import signal
import socket
import subprocess
import sys
import time

ROM = [
    0x40000040,  # ets_printf
    0x40000128,  # esp_rom_spiflash_erase_sector
    0x4000012C,  # esp_rom_spiflash_write
    0x40000130,  # esp_rom_spiflash_read
    0x40000140,  # esp_rom_spiflash_unlock
    0x400004D8,  # Cache_Invalidate_ICache_All
    0x40000524,  # Cache_Suspend_ICache
    0x40000528,  # Cache_Resume_ICache
]
PRINTF = 0x40000040
ARGS = {0x40000128: 1, 0x4000012C: 3, 0x40000130: 3, 0x40000528: 1}
BOOTLOADER = range(0x403A0000, 0x403C4000)
JUMP_FORMAT = b"c3-boot: jumping to %x\n"
TIMEOUT = 600
DEADLINE = 900


class Gdb:
    def __init__(self, port):
        deadline = time.time() + 10
        while True:
            try:
                self.sock = socket.create_connection(("127.0.0.1", port))
                break
            except OSError:
                if time.time() > deadline:
                    raise
                time.sleep(0.1)
        self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.sock.settimeout(TIMEOUT)
        self.buf = b""
        self.acks = True

    def _read(self, n=1):
        while len(self.buf) < n:
            chunk = self.sock.recv(65536)
            if not chunk:
                raise EOFError("QEMU closed the GDB connection")
            self.buf += chunk
        out, self.buf = self.buf[:n], self.buf[n:]
        return out

    def command(self, packet):
        body = packet.encode()
        checksum = sum(body) % 256
        self.sock.sendall(b"$" + body + b"#" + f"{checksum:02x}".encode())
        while self.acks:
            c = self._read()
            if c == b"+":
                break
            if c == b"-":
                self.sock.sendall(b"$" + body + b"#" + f"{checksum:02x}".encode())
        while self._read() != b"$":
            pass
        reply = b""
        while True:
            c = self._read()
            if c == b"#":
                self._read(2)
                break
            reply += c
        if self.acks:
            self.sock.sendall(b"+")
        return reply.decode()

    def regs(self):
        """x0 through x31 and pc."""
        text = self.command("g")
        words = [text[i : i + 8] for i in range(0, 33 * 8, 8)]
        return [int.from_bytes(bytes.fromhex(w), "little") for w in words]

    def memory(self, addr, length):
        return bytes.fromhex(self.command(f"m{addr:x},{length:x}"))

    def c_string(self, addr):
        data = self.memory(addr, 256)
        return data.split(b"\0", 1)[0]


def format_args(fmt):
    """One argument per % conversion, not counting %%."""
    return fmt.replace(b"%%", b"").count(b"%")


def main():
    qemu, flash, efuse, halt_hex = sys.argv[1:]
    signal.alarm(DEADLINE)
    halt = int(halt_hex, 16)
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        port = s.getsockname()[1]
    proc = subprocess.Popen(
        [
            qemu, "-machine", "esp32c3", "-display", "none", "-monitor", "none",
            "-serial", "null",
            "-drive", f"file={flash},if=mtd,format=raw",
            "-drive", f"file={efuse},if=none,format=raw,id=efuse",
            "-global", "driver=nvram.esp32c3.efuse,property=drive,value=efuse",
            "-gdb", f"tcp:127.0.0.1:{port}", "-S",
        ],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    try:
        gdb = Gdb(port)
        if gdb.command("QStartNoAckMode") == "OK":
            gdb.acks = False
        gdb.command("?")
        breakpoints = set(ROM + [halt])
        for b in breakpoints:
            if gdb.command(f"Z0,{b:x},4") != "OK":
                sys.exit(f"QEMU refused a breakpoint at {b:x}")
        entry = None
        while True:
            stop = gdb.command("c")
            if not stop.startswith(("T", "S")):
                sys.exit(f"unexpected stop reply {stop!r}")
            r = gdb.regs()
            pc, ra, a = r[32], r[1], r[10:12]
            if pc == halt:
                print(f"halt {a[0]:x}")
                return
            if pc == entry:
                print(f"jump {pc:x} {a[0]:x}")
                return
            if pc in ROM and ra in BOOTLOADER:
                fmt = gdb.c_string(a[0]) if pc == PRINTF else b""
                count = 1 + format_args(fmt) if pc == PRINTF else ARGS.get(pc, 0)
                args = "".join(f" {v:x}" for v in r[10 : 10 + count])
                print(f"call {pc:x}{args}", flush=True)
                if pc == PRINTF and fmt == JUMP_FORMAT:
                    entry = a[1]
                    gdb.command(f"Z0,{entry:x},4")
                    breakpoints.add(entry)
            # Step off the breakpoint before continuing.
            gdb.command(f"z0,{pc:x},4")
            gdb.command("s")
            gdb.command(f"Z0,{pc:x},4")
    finally:
        proc.kill()
        proc.wait()


if __name__ == "__main__":
    main()
