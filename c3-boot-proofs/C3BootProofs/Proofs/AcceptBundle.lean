import C3BootProofs.Proofs.AcceptBundleSegs

/-!
# `boot_main`'s first closure: the bundle stage

From 0x1816 to the call to `sigstore::verify` at 0x1A46: move the trust root
to `sp + 0x1870`, read the bundle part with a `Reader` at `sp + 0xDD0`
(`Reader::magic`, `Reader::version_1`, and `bundle::field` six times), and
lay the `Bundle` out at `sp + 0x1320` for `sigstore::verify`, with the
image's digest at `sp + 0x108`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

end C3.RV32.Ac
