import C3BootProofs.Models.PrimeCerts
import C3BootProofs.Spec.Ed25519

/-!
# The curve primes are prime

The field primes and group orders of P-256 and P-384, and Ed25519's field
prime and base-point order, from the Pratt certificates in `PrimeCerts`.
These discharge the `IsPrime` hypotheses of the ECDSA models.
-/

namespace C3.Models

theorem p256_prime : IsPrime C3.p256.p := PrimeCerts.prime_p256

theorem p256_n_prime : IsPrime C3.p256.n := PrimeCerts.prime_p256_n

theorem p384_prime : IsPrime C3.p384.p := PrimeCerts.prime_p384

theorem p384_n_prime : IsPrime C3.p384.n := PrimeCerts.prime_p384_n

theorem ed25519_p_prime : IsPrime (2 ^ 255 - 19) := PrimeCerts.prime_ed25519_p

theorem ed25519_L_prime : IsPrime (2 ^ 252 + 27742317777372353535851937790883648493) :=
  PrimeCerts.prime_ed25519_L

theorem ed25519_spec_p_prime : IsPrime C3.Ed25519.p := ed25519_p_prime

theorem ed25519_spec_L_prime : IsPrime C3.Ed25519.L := ed25519_L_prime

end C3.Models
