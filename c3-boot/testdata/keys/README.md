# Development keys

These Ed25519 keys are for tests and QEMU runs only. Their seeds are public,
so anyone can sign a trust root that a bootloader built with them accepts.
Never build a bootloader for a real device with `genesis-dev.pub`. The
bootloader build requires `C3_GENESIS`: set it to the production genesis key
file, or to `dev` to use these keys. A `dev` build prints a warning on every
boot.

- `genesis-dev-1.seed` through `genesis-dev-4.seed`: hex-encoded 32-byte
  seeds.
- `genesis-dev.pub`: the four public keys, 128 bytes, in index order.
