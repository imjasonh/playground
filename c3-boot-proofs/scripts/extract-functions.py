#!/usr/bin/env python3
"""Writes C3BootProofs/Image/Bootloader.lean: the bytes of the bootloader
functions that have machine-code proofs, taken from the bootloader image.

The bytes come from the ESP image's segments, which are what the ROM loads,
at the addresses and sizes that the ELF's symbol table gives. Code without a
symbol of its own, such as `memcpy`'s body, is named by the call that
reaches it: the `auipc; jalr` pair at an offset of an extracted function,
decoded the way the CPU decodes it. The module
also records the image's SHA-256, which must equal
c3-boot/bootloader/dev-image.sha256. CI regenerates the module and fails if
it differs from the committed one, so the proofs are about the pinned image.

Usage: extract-functions.py ESP_IMAGE ELF NM OUT [EXTRA...]
"""

import hashlib
import re
import struct
import subprocess
import sys

# Lean name, then the demangled symbol, the mangled one when two functions
# demangle alike, or the Lean name of an earlier function and the offset of a
# call in it. A demangled symbol leaves out the ` (.N)` that LLVM appends to
# local copies, because N changes whenever a copy is added or removed
# anywhere in the program. When copies with different code share a name, a
# third element picks one by the start of its shape hash (see `shape_hash`).
FUNCTIONS = [
    ("crc32", "c3_verify::bootstate::crc32"),
    ("readerBytes", "<c3_verify::reader::Reader>::bytes"),
    ("readerArray4", "<c3_verify::reader::Reader>::array::<4>"),
    ("readerU32", "<c3_verify::reader::Reader>::u32"),
    ("manifestPart", "c3_verify::manifest::part"),
    ("manifestParse", "c3_verify::manifest::parse"),
    ("readerMagic", "<c3_verify::reader::Reader>::magic"),
    ("readerU16", "<c3_verify::reader::Reader>::u16"),
    ("readerVersion1", "<c3_verify::reader::Reader>::version_1"),
    ("readerReserved", "<c3_verify::reader::Reader>::reserved"),
    ("readerU8", "<c3_verify::reader::Reader>::u8"),
    ("segmentPhysical", "<c3_verify::image::Segment>::physical"),
    ("imageParse", "c3_verify::image::parse"),
    ("memcpyStub", "memcpy"),
    ("memcpyBody", ("memcpyStub", 0x00)),
    ("memset", "memset"),
    ("borrowingSub", "crypto_bigint::primitives::borrowing_sub"),
    ("subInner", "p256::arithmetic::field::field_impl::sub_inner"),
    ("wideMul", "crypto_bigint::uint::mul::karatsuba::widening_mul_fixed::<8, 8>"),
    ("fieldMul", "<p256::arithmetic::field::FieldElement>::multiply"),
    ("fieldAdd", "p256::arithmetic::field::field_impl::add"),
    ("fieldSub", "p256::arithmetic::field::field_impl::sub"),
    ("fieldDouble", "<p256::arithmetic::field::FieldElement as ff::Field>::double"),
    ("pointAdd", "<primeorder::point_arithmetic::EquationAIsMinusThree as "
     "primeorder::point_arithmetic::sealed::PointArithmetic<p256::NistP256>>::add_assign"),
    ("sha256Compress", "sha2::sha256::compress256"),
    ("rangeFromIndex", "<core::ops::range::RangeFrom<usize> as core::slice::index::SliceIndex<[u8]>>::index"),
    ("shaUpdate", "<sha2::Sha256 as digest::Update>::update"),
    ("shaUpdateBlocks", ("shaUpdate", 0x62)),
    ("shaFinalize", "<sha2::Sha256 as digest::digest::Digest>::finalize"),
    ("shaZero32", ("shaFinalize", 0x18)),
    ("shaFinBlock", ("shaFinalize", 0xB0)),
    ("shaFinish", "<c3_crypto::sha::Sha256>::finish"),
    ("sha256Fn", "c3_crypto::sha::sha256"),
    ("sha512Compress", "sha2::sha512::compress512"),
    ("rootFromInclusion", "c3_verify::merkle::root_from_inclusion"),
    ("mulMont12", "crypto_bigint::modular::mul::mul_montgomery_form::<12>"),
    ("uintSelect12", "<crypto_bigint::uint::Uint<12>>::select"),
    ("sqMont12", "crypto_bigint::modular::mul::square_montgomery_form::<12>"),
    ("p384Add", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<"
     "p384::arithmetic::field::FieldParams, 12>>::add"),
    ("p384Sub", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<"
     "p384::arithmetic::field::FieldParams, 12>>::sub"),
    ("p384Double", "<p384::arithmetic::field::FieldElement as ff::Field>::double"),
    ("feReduce", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625>::reduce"),
    ("feMul", "<&curve25519_dalek::backend::serial::u32::field::FieldElement2625 as core::ops::arith::Mul>::mul"),
    ("feSquareInner", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625>::square_inner"),
    ("feSquare", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625>::square"),
    ("fePow2k", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625>::pow2k"),
    ("flashRead", "c3_bootloader::flash::read"),
    ("romFlashReadWords", "c3_bootloader::rom::flash_read_words"),
    ("feAdd", "<&curve25519_dalek::backend::serial::u32::field::FieldElement2625 as core::ops::arith::Add>::add"),
    ("selectI64", "<ctutils::choice::Choice>::select_i64"),
    ("feSub", "<&curve25519_dalek::backend::serial::u32::field::FieldElement2625 as core::ops::arith::Sub>::sub"),
    ("wideMul12x2", "crypto_bigint::uint::mul::karatsuba::widening_mul_fixed::<12, 2>"),
    ("wideMul8x2", "crypto_bigint::uint::mul::karatsuba::widening_mul_fixed::<8, 2>"),
    ("edDouble", "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double"),
    ("p384Mul", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<p384::arithmetic::field::FieldParams, 12>>::mul"),
    ("p384Sqr", "<p384::arithmetic::field::FieldElement as ff::Field>::square"),
    ("p384PtDouble", "<primeorder::projective::ProjectivePoint<p384::NistP384> as group::Group>::double"),
    ("uintSelect2", "<crypto_bigint::uint::Uint<2>>::select"),
    ("condNeg12", "crypto_bigint::modular::safegcd::conditional_negate_in_place_wide::<12, 2>"),
    ("uintSelect8", "<crypto_bigint::uint::Uint<8>>::select"),
    ("condNeg8", "crypto_bigint::modular::safegcd::conditional_negate_in_place_wide::<8, 2>"),
    ("absSign2", "<crypto_bigint::int::Int<2>>::abs_sign"),
    ("fromI64", "<crypto_bigint::int::Int<2>>::from_i64"),
    ("p384PtAdd", "<primeorder::point_arithmetic::EquationAIsMinusThree as "
     "primeorder::point_arithmetic::sealed::PointArithmetic<p384::NistP384>>::add_assign"),
    ("fieldSquare", "<p256::arithmetic::field::FieldElement as ff::Field>::square"),
    ("p256PtDouble", "<primeorder::projective::ProjectivePoint<p256::NistP256> as group::Group>::double"),
    ("shr12", "crypto_bigint::modular::safegcd::shr_in_place_wide::<12, 2>"),
    ("leadMut12", ("shr12", 0x92)),
    ("trailing12", ("shr12", 0xA4)),
    ("shr8", "crypto_bigint::modular::safegcd::shr_in_place_wide::<8, 2>"),
    ("leadMut8", ("shr8", 0x92)),
    ("trailing8", ("shr8", 0xA4)),
    ("feToBytes", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625>::to_bytes"),
    ("lincomb12", "<crypto_bigint::modular::safegcd::SignedInt<12>>::lincomb_int::<2>"),
    ("blackBoxU8", "subtle::black_box::<u8>"),
    ("ctEqU8", "<u8 as subtle::ConstantTimeEq>::ct_eq"),
    ("ctEqSlice", "<[u8] as subtle::ConstantTimeEq>::ct_eq"),
    ("memcmp", "memcmp"),
    ("uintRefIsNonzero", "<crypto_bigint::uint::ref_type::UintRef>::is_nonzero"),
    ("lshrdi3", "__lshrdi3"),
    ("asProjective", "<curve25519_dalek::backend::serial::curve_models::CompletedPoint>::as_projective"),
    ("asExtended", "<curve25519_dalek::backend::serial::curve_models::CompletedPoint>::as_extended"),
    ("p384Neg", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<"
     "p384::arithmetic::field::FieldParams, 12>>::neg"),
    ("uint12IsNonzero", ("p384Neg", 0x16)),
    ("derTlv", "<c3_verify::der::Der>::tlv"),
    ("derElement", "<c3_verify::der::Der>::element"),
    ("derOid", "<c3_verify::der::Der>::oid"),
    ("derNested", "<c3_verify::der::Der>::nested"),
    ("derSequence", "<c3_verify::der::Der>::sequence"),
    ("equalSameLength", "<u8 as core::slice::cmp::SlicePartialEq<u8>>::equal_same_length"),
    ("sliceEq", "<[u8] as core::cmp::PartialEq>::eq"),
    ("lincomb8", "<crypto_bigint::modular::safegcd::SignedInt<8>>::lincomb_int::<2>"),
    ("scalar29Sub", "<curve25519_dalek::backend::serial::u32::scalar::Scalar29>::sub"),
    ("scalar29Index", ("scalar29Sub", 0x4A)),
    ("scalar29IndexMut", ("scalar29Sub", 0x70)),
    ("scalar29MontMul", "<curve25519_dalek::backend::serial::u32::scalar::Scalar29>::montgomery_mul"),
    ("mulMont8", "crypto_bigint::modular::mul::mul_montgomery_form::<8>"),
    ("p256ScalarMul", "<p256::arithmetic::scalar::Scalar as core::ops::arith::Mul>::mul"),
    ("lincombShift12", "<crypto_bigint::modular::safegcd::SignedInt<12>>::lincomb_int_reduce_shift::<2>"),
    ("lincombShift8", "<crypto_bigint::modular::safegcd::SignedInt<8>>::lincomb_int_reduce_shift::<2>"),
    ("lowest12", "<crypto_bigint::modular::safegcd::SignedInt<12>>::lowest"),
    ("lowest8", "<crypto_bigint::modular::safegcd::SignedInt<8>>::lowest"),
    ("updateFg12", "crypto_bigint::modular::safegcd::update_fg::<12>"),
    ("updateFg8", "crypto_bigint::modular::safegcd::update_fg::<8>"),
    ("norm12", "<crypto_bigint::modular::safegcd::SignedInt<12>>::norm"),
    ("uint8IsNonzero", "<crypto_bigint::uint::Uint<8>>::is_nonzero"),
    ("norm8", "<crypto_bigint::modular::safegcd::SignedInt<8>>::norm"),
    ("toUintResize2", "<crypto_bigint::uint::ref_type::UintRef>::to_uint_resize::<2>"),
    ("lincombShiftMod12", "<crypto_bigint::modular::safegcd::SignedInt<12>>::lincomb_int_reduce_shift_mod::<2>"),
    ("lincombShiftMod8", "<crypto_bigint::modular::safegcd::SignedInt<8>>::lincomb_int_reduce_shift_mod::<2>"),
    ("updateDe12", "crypto_bigint::modular::safegcd::update_de::<12>"),
    ("updateDe8", "crypto_bigint::modular::safegcd::update_de::<8>"),
    ("derSet", "<c3_verify::der::Der>::set"),
    ("derOctetString", "<c3_verify::der::Der>::octet_string"),
    ("derBitString", "<c3_verify::der::Der>::bit_string"),
    ("derInteger", "<c3_verify::der::Der>::integer"),
    ("derBooleanTrue", "<c3_verify::der::Der>::boolean_true"),
    ("derOptional", "<c3_verify::der::Der>::optional"),
    ("uint12Eq", "<crypto_bigint::uint::Uint<12>>::eq"),
    ("uint8Eq", "<crypto_bigint::uint::Uint<8>>::eq"),
    ("lessThanLe", "c3_crypto::less_than_le"),
    ("inScalarRange", "c3_crypto::ecdsa::in_scalar_range"),
    ("p384ScalarMul", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<p384::arithmetic::scalar::ScalarParams, 12>>::mul"),
    ("p384ScalarNew", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<p384::arithmetic::scalar::ScalarParams, 12>>::new"),
    ("u32Min", "crypto_bigint::primitives::u32_min"),
    ("sliceReverse", "<[u8]>::reverse"),
    ("uintRefIsZero", "<crypto_bigint::uint::ref_type::UintRef>::is_zero"),
    ("choiceNot", "<subtle::Choice as core::ops::bit::Not>::not"),
    ("splitAt12", "<crypto_bigint::uint::ref_type::UintRef>::split_at", "932627e48b26"),
    ("limbCtEq", "<[crypto_bigint::limb::Limb] as ctutils::traits::ct_eq::CtEq>::ct_eq"),
    ("uint12CtEq", "<crypto_bigint::uint::Uint<12> as ctutils::traits::ct_eq::CtEq>::ct_eq"),
    ("montRetrieve12", "crypto_bigint::modular::reduction::montgomery_retrieve::<12>"),
    ("p384FieldRetrieve", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<p384::arithmetic::field::FieldParams, 12>>::retrieve"),
    ("sliceCtAssign", "<[u32] as ctutils::traits::ct_assign::CtAssign>::ct_assign"),
    ("uint12CtAssign", "<crypto_bigint::uint::Uint<12> as ctutils::traits::ct_assign::CtAssign>::ct_assign"),
    ("copyFromSliceU8", "core::slice::copy_from_slice_impl::<u8>"),
    ("zipSkipNext", "<core::iter::adapters::zip::Zip<core::iter::adapters::skip::Skip<core::slice::iter::IterMut<u8>>, core::slice::iter::Iter<u8>> as core::iter::traits::iterator::Iterator>::next"),
    ("derPositiveInteger", "<c3_verify::der::Der>::positive_integer"),
    ("derScalar48", "c3_verify::der::scalar::<48>"),
    ("derScalar32", "c3_verify::der::scalar::<32>"),
    ("ecdsaSignature48", "c3_verify::der::ecdsa_signature::<48>"),
    ("derIntegerIs", "<c3_verify::der::Der>::integer_is"),
    ("derAlgorithm", "<c3_verify::der::Der>::algorithm"),
    ("listsOid", "c3_verify::der::lists_oid"),
    ("checkpointLine", "c3_verify::checkpoint::line"),
    ("timeDigits2", "c3_verify::time::digits::<2>"),
    ("base64DecodeInto", "c3_verify::base64::decode_into"),
    ("scalarIsZero384", "<elliptic_curve::scalar::value::ScalarValue<p384::NistP384>>::is_zero"),
    ("scalarIsZero256", "<elliptic_curve::scalar::value::ScalarValue<p256::NistP256>>::is_zero"),
    ("tagFromU8", "<sec1::point::Tag>::from_u8"),
    ("tagMessageLen", "<sec1::point::Tag>::message_len"),
    ("p256FieldNeg", "<p256::arithmetic::field::FieldElement>::neg"),
    ("sliceNe", "<&[u8] as core::cmp::PartialEq>::ne"),
    ("arr32Eq", "_RNvXNtNtCs2opbmDwVT5n_4core5array8equalityAhj20_NtNtB6_3cmp9PartialEq2eqCslBQrogs5cN1_9c3_verify"),
    ("arr32Ne", "<[u8; 32] as core::cmp::PartialEq>::ne"),
    ("choiceCtEq", "<subtle::Choice as subtle::ConstantTimeEq>::ct_eq"),
    ("splitAt8", "<crypto_bigint::uint::ref_type::UintRef>::split_at", "0d950e4d6222"),
    ("tagAndThen", "<core::result::Result<u8, sec1::error::Error>>::and_then::<sec1::point::Tag, <sec1::point::Tag>::from_u8>"),
    ("montyScalarCtEq384", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<p384::arithmetic::scalar::ScalarParams, 12> as subtle::ConstantTimeEq>::ct_eq"),
    ("ashldi3", "__ashldi3"),
    ("dateTime", "c3_verify::time::date_time"),
    ("leadingZeros", "<crypto_bigint::uint::ref_type::UintRef>::leading_zeros"),
    ("condSelect384", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<p384::arithmetic::field::FieldParams, 12> as subtle::ConditionallySelectable>::conditional_select"),
    ("condSelect256", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<p256::arithmetic::field::FieldParams, 8> as subtle::ConditionallySelectable>::conditional_select"),
    ("nonZero384", "<elliptic_curve::scalar::nonzero::NonZeroScalar<p384::NistP384>>::new"),
    ("uint8CtEq", "<crypto_bigint::uint::Uint<8> as ctutils::traits::ct_eq::CtEq>::ct_eq"),
    ("p256FieldRetrieve", "<crypto_bigint::modular::const_monty_form::ConstMontyForm<p256::arithmetic::field::FieldParams, 8>>::retrieve"),
    ("ctMap384", "<subtle::CtOption<primefield::monty::MontyFieldElement<p384::arithmetic::field::FieldParams, 12>>>::map::<p384::arithmetic::field::FieldElement, p384::arithmetic::field::FieldElement>"),
    ("ctMap256", "<subtle::CtOption<primefield::monty::MontyFieldElement<p256::arithmetic::field::FieldParams, 8>>>::map::<p256::arithmetic::field::FieldElement, p256::arithmetic::field::FieldElement>"),
    ("unwrapOr384", "<subtle::CtOption<primeorder::affine::AffinePoint<p384::NistP384>>>::unwrap_or"),
    ("unwrapOr256", "<subtle::CtOption<primeorder::affine::AffinePoint<p256::NistP256>>>::unwrap_or"),
    ("p256ScalarCtEq", "<p256::arithmetic::scalar::Scalar as subtle::ConstantTimeEq>::ct_eq"),
    ("nonZero256", "<elliptic_curve::scalar::nonzero::NonZeroScalar<p256::NistP256>>::new"),
    ("arr32EqCrypto", "_RNvXNtNtCs2opbmDwVT5n_4core5array8equalityAhj20_NtNtB6_3cmp9PartialEq2eqCspC4dVFUdfd_9c3_crypto"),
    ("feIsNegative", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625>::is_negative"),
    ("isSha256", "c3_verify::tsa::is_sha256"),
    ("feLoad3", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625>::from_bytes::load3_at"),
    ("feLoad4", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625>::from_bytes::load4_at"),
    ("feCtEq", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as subtle::ConstantTimeEq>::ct_eq"),
    ("feCondAssign", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as subtle::ConditionallySelectable>::conditional_assign"),
    ("feNeg", "<&curve25519_dalek::backend::serial::u32::field::FieldElement2625 as core::ops::arith::Neg>::neg"),
    ("asProjNiels", "<curve25519_dalek::edwards::EdwardsPoint>::as_projective_niels"),
    ("edAddNiels", "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::add"),
    ("edSubNiels", "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Sub<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::sub"),
    ("scalar29Pack", "<curve25519_dalek::backend::serial::u32::scalar::Scalar29>::pack"),
    ("pow22501", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625>::pow22501"),
    ("nonAdjacentForm", "<curve25519_dalek::scalar::Scalar>::non_adjacent_form"),
    ("incrementLimb", "<wnaf::limb_buffer::LimbBuffer>::increment_limb"),
    ("feCondNeg", "<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as subtle::ConditionallyNegatable>::conditional_negate"),
    ("isSmallOrder", "<curve25519_dalek::edwards::EdwardsPoint>::is_small_order"),
    ("halt", "c3_bootloader::halt"),
    ("beginUnwind", "__rustc::rust_begin_unwind"),
    ("panicFmt", "core::panicking::panic_fmt"),
    ("assertFailedInner", "core::panicking::assert_failed_inner"),
    ("corePanic", "core::panicking::panic"),
    ("panicBoundsCheck", "core::panicking::panic_bounds_check"),
    ("expectFailed", "core::option::expect_failed"),
    ("unwrapFailed", "core::result::unwrap_failed"),
    ("lenMismatchFail", "core::slice::copy_from_slice_impl::len_mismatch_fail"),
    ("sliceIndexFail", "core::slice::index::slice_index_fail"),
    ("assertFailedUsize", "core::panicking::assert_failed::<usize, usize>"),
    ("assertFailedU8", "core::panicking::assert_failed::<u8, u8>"),
    ("expectUsize", "<core::result::Result<usize, core::num::error::TryFromIntError>>::expect"),
    ("expectTag", "<core::result::Result<sec1::point::Tag, sec1::error::Error>>::expect"),
    ("encodedPointTag", "<sec1::point::EncodedPoint<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>>>::tag"),
    ("encodedPointIsIdentity", "<sec1::point::EncodedPoint<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>>>::is_identity"),
    ("nafSelect", "<curve25519_dalek::window::NafLookupTable5<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::select"),
    ("ctUnwrap384", "<subtle::CtOption<elliptic_curve::scalar::nonzero::NonZeroScalar<p384::NistP384>>>::unwrap"),
    ("ctUnwrap256", "<subtle::CtOption<elliptic_curve::scalar::nonzero::NonZeroScalar<p256::NistP256>>>::unwrap"),
    ("sha512UpdateArr32", "<sha2::Sha512 as digest::digest::Digest>::update::<&[u8; 32]>"),
    ("zeroArray64", "<hybrid_array::Array<u8, typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>>>::try_from_fn::<core::convert::Infallible, <hybrid_array::Array<u8, typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>>>::from_fn<<hybrid_array::Array<u8, typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>> as core::default::Default>::default::{closure#0}>::{closure#0}>"),
    ("zeroArray48", "<hybrid_array::Array<u8, typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>>>::try_from_fn::<core::convert::Infallible, <hybrid_array::Array<u8, typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>>>::from_fn<<hybrid_array::Array<u8, typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>, typenum::bit::B0>> as core::default::Default>::default::{closure#0}>::{closure#0}>"),
    ("ctIntoAffine256", "<subtle::CtOption<primeorder::affine::AffinePoint<p256::NistP256>> as core::convert::Into<ctutils::ct_option::CtOption<primeorder::affine::AffinePoint<p256::NistP256>>>>::into"),
    ("ctIntoAffine384", "<subtle::CtOption<primeorder::affine::AffinePoint<p384::NistP384>> as core::convert::Into<ctutils::ct_option::CtOption<primeorder::affine::AffinePoint<p384::NistP384>>>>::into"),
    ("sha512FinBlock", "<sha2::block_api::Sha512VarCore as digest::block_api::VariableOutputCore>::finalize_variable_core::{closure#0}"),
    ("sha384UpdateBlocks", "<sha2::Sha384 as digest::Update>::update::{closure#0}"),
    ("merkleNodeHash", "c3_verify::merkle::node_hash"),
    ("toBeBytes12", "<crypto_bigint::uint::Uint<12> as crypto_bigint::encoding::ArrayEncoding>::to_be_byte_array"),
    ("toBeBytes8", "<crypto_bigint::uint::Uint<8> as crypto_bigint::encoding::ArrayEncoding>::to_be_byte_array"),
    ("fromBeSliceTrunc12", "<crypto_bigint::uint::Uint<12> as crypto_bigint::encoding::Encoding>::from_be_slice_truncated"),
    ("fromBeSliceTrunc8", "<crypto_bigint::uint::Uint<8> as crypto_bigint::encoding::Encoding>::from_be_slice_truncated"),
    ("edVerifyingKeyFromBytes", "<ed25519_dalek::verifying::VerifyingKey>::from_bytes"),
    ("sha256Parts", "c3_crypto::sha::sha256_parts"),
    ("ed25519PublicKeyOk", "c3_crypto::ed25519_public_key_ok"),
    ("sha512Update", "<sha2::Sha512 as digest::Update>::update"),
    ("scalarFromSlice256", "<elliptic_curve::scalar::value::ScalarValue<p256::NistP256>>::from_slice"),
    ("scalarFromSlice384", "<elliptic_curve::scalar::value::ScalarValue<p384::NistP384>>::from_slice"),
    ("nafTableFrom", "<curve25519_dalek::window::NafLookupTable5<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> as core::convert::From<&curve25519_dalek::edwards::EdwardsPoint>>::from"),
    ("x509ReadTime", "c3_verify::x509::read_time"),
    ("generalizedTime", "c3_verify::time::generalized_time"),
    ("bytes2scalar256", "ecdsa::hazmat::bytes2scalar::<p256::NistP256>"),
    ("fillLimbsBeTrunc", "crypto_bigint::uint::encoding::fill_limbs_from_be_slice_truncated"),
    ("bytes2scalar384", "ecdsa::hazmat::bytes2scalar::<p384::NistP384>"),
    ("base64EncodeTo", "c3_verify::base64::encode_to::<c3_crypto::sha::Sha256>"),
    ("p256FromRepr", "<p256::arithmetic::field::FieldElement as ff::PrimeField>::from_repr"),
    ("p384FromRepr", "<p384::arithmetic::field::FieldElement as ff::PrimeField>::from_repr"),
    ("wnafForm", "wnaf::wnaf_form::<&[u8]>"),
    ("edDecompress", "<curve25519_dalek::edwards::CompressedEdwardsY>::decompress"),
    ("p384FromSec1", "<ecdsa::verifying::VerifyingKey<p384::NistP384>>::from_sec1_bytes"),
    ("p256FromSec1", "<ecdsa::verifying::VerifyingKey<p256::NistP256>>::from_sec1_bytes"),
    ("p384Decompress", "<primeorder::affine::AffinePoint<p384::NistP384> as elliptic_curve::point::DecompressPoint<p384::NistP384>>::decompress"),
    ("p256Decompress", "<primeorder::affine::AffinePoint<p256::NistP256> as elliptic_curve::point::DecompressPoint<p256::NistP256>>::decompress"),
    ("p384VerifyPrehash", "c3_crypto::ecdsa::p384_verify_prehash"),
    ("ed25519Verify", "c3_crypto::ed25519_verify"),
    ("sigstoreVerify", "c3_verify::sigstore::verify"),
    ("eqArr97", "<&[u8; 97] as core::cmp::PartialEq>::eq"),
    ("fulcioIterNext", "<core::iter::adapters::map_while::MapWhile<core::slice::iter::Iter<core::option::Option<c3_verify::trustroot::FulcioIntermediate>>, <core::option::Option<c3_verify::trustroot::FulcioIntermediate>>::as_ref> as core::iter::traits::iterator::Iterator>::next"),
    ("fulcioIterNth", "<core::iter::adapters::map_while::MapWhile<core::slice::iter::Iter<core::option::Option<c3_verify::trustroot::FulcioIntermediate>>, <core::option::Option<c3_verify::trustroot::FulcioIntermediate>>::as_ref> as core::iter::traits::iterator::Iterator>::nth"),
    ("fulcioEnumNext", "<core::iter::adapters::enumerate::Enumerate<core::iter::adapters::map_while::MapWhile<core::slice::iter::Iter<core::option::Option<c3_verify::trustroot::FulcioIntermediate>>, <core::option::Option<c3_verify::trustroot::FulcioIntermediate>>::as_ref>> as core::iter::traits::iterator::Iterator>::next"),
    ("bootstateDecode", "c3_verify::bootstate::decode"),
    ("bundleField", "c3_verify::bundle::field"),
    ("bootFn", "c3_bootloader::boot"),
    ("bootMainClosure0", "c3_bootloader::boot_main::{closure#0}"),
    ("bootMainClosure1", "c3_bootloader::boot_main::{closure#1}"),
    ("bootMain", "boot_main"),
    ("sha384Fn", "c3_crypto::sha::sha384"),
    ("p256VerifyPrehash", "c3_crypto::ecdsa::p256_verify_prehash"),
    ("stripPrefix", "<[u8]>::strip_prefix::<[u8]>"),
    ("ecdsaSignature32", "c3_verify::der::ecdsa_signature::<32>"),
    ("allAsciiDigit", "<core::slice::iter::Iter<u8> as core::iter::traits::iterator::Iterator>"
     "::all::<<u8>::is_ascii_digit>"),
    ("timeDigits4", "c3_verify::time::digits::<4>"),
    ("timeRfc3339", "c3_verify::time::rfc3339"),
    ("jsonSkipWs", "c3_verify::json::skip_ws"),
    ("jsonStringEnd", "c3_verify::json::string_end"),
    ("jsonKeyEnd", "c3_verify::json::key_end"),
    ("jsonLiteralEnd", "c3_verify::json::literal_end"),
    ("jsonNumberEnd", "c3_verify::json::number_end"),
    ("jsonReadItem", "c3_verify::json::read_item"),
    ("jsonNextMember", "<c3_verify::json::Members>::next_member"),
    ("jsonNextElement", "<c3_verify::json::Elements>::next_element"),
    ("jsonMembers", "<c3_verify::json::Value>::members"),
    ("jsonElements", "<c3_verify::json::Value>::elements"),
    ("jsonGet", "<c3_verify::json::Value>::get"),
    ("jsonField", "<c3_verify::json::Value>::field"),
    ("jsonStr", "<c3_verify::json::Value>::str"),
    ("jsonU64", "<c3_verify::json::Value>::u64"),
    ("jsonParse", "c3_verify::json::parse"),
    ("tufHexValue", "c3_verify::tuf::hex_value"),
    ("tufHexDecode", "c3_verify::tuf::hex_decode"),
    ("tufPemSpki", "c3_verify::tuf::pem_spki"),
    ("tufIndexDoc", "<c3_verify::tuf::Index>::doc"),
    ("tufReadDoc", "c3_verify::tuf::read_doc::<c3_bootloader::FlashPart>"),
    ("tufParseMetadata", "c3_verify::tuf::parse_metadata"),
    ("tufParseRoot", "c3_verify::tuf::parse_root"),
    ("tufExpires", "c3_verify::tuf::expires"),
    ("tufRoleKeysRead", "<c3_verify::tuf::RoleKeys>::read"),
    ("tufRoleKeysMet", "<c3_verify::tuf::RoleKeys>::met"),
    ("trustedRootDecode", "c3_verify::trusted_root::decode"),
    ("trustedRootValidFor", "c3_verify::trusted_root::valid_for"),
    ("trustedRootReadChain", "c3_verify::trusted_root::read_chain"),
    ("flashPartRead", "<c3_bootloader::FlashPart as c3_verify::tuf::Source>::read"),
    ("efuseProgramRun", "c3_bootloader::efuse::program::run"),
]

# The code that runs from the ROM's jump to `_start` until `boot_main`,
# written to the eleventh output. Same fields as `FUNCTIONS`. `_start` is
# assembly without a size, so its code runs to the next function.
FUNCTIONS_RESET = [
    ("startEntry", "_start"),
    ("setupFn", "setup"),
    ("watchdogArm", "c3_bootloader::watchdog::arm"),
    ("clockRun160", "c3_bootloader::clock::run_at_160mhz"),
]

# Lean name, then the Lean name of an extracted function, the offset of a
# `lui; addi` pair in it that forms an address, the data's size, and,
# optionally, the data's offset from that address. A size of 0 names an
# address without data.
DATA = [
    ("curveB", "pointAdd", 0x12E, 32),
    ("u2Max", "lincombShiftMod12", 0xF0, 8),
    ("shaK", "sha256Compress", 0xB8, 256),
    ("shaIV", "sha256Fn", 0x12, 32),
    ("p384Modulus", "p384Add", 0x66, 48),
    ("sha512K", "sha512Compress", 0x1F8, 640),
    ("p384B", "p384PtDouble", 0x9E, 48),
    ("u2Zero", "condNeg12", 0x7E, 8),
    ("u2One", "condNeg12", 0x86, 8),
    ("scalarL", "scalar29Sub", 0x36, 36),
    ("p384Order", "p384ScalarMul", 0x0, 48),
    ("p384ScalarR2", "p384ScalarNew", 0x0, 48, 0x60),
    ("p256Zero", "p256FieldNeg", 0x2, 32),
    ("scalarZero384", "nonZero384", 0xE, 48),
    ("sha256Oid", "isSha256", 0x26, 9),
    ("edwardsD2", "asProjNiels", 0x4A, 40),
    ("merklePrefix", "merkleNodeHash", 0x4, 1),
    ("p256Modulus", "p256FieldRetrieve", 0x2A, 32, -4),
    ("p384R2", "p384FromRepr", 0xB2, 48, 0x60),
    ("p256R2", "p256FromRepr", 0xB0, 32, 0x40),
    ("b2sOrder384", "bytes2scalar384", 0x1A, 48),
    ("b2sOrder256", "bytes2scalar256", 0x16, 32),
    ("edOne", "isSmallOrder", 0x98, 40),
    ("edD", "edDecompress", 0x102, 40),
    ("edSqrtM1", "edDecompress", 0x1F8, 40),
    ("b64Alphabet", "base64EncodeTo", 0x28, 64),
    ("regionEnds", "imageParse", 0x250, 16),
    ("regionStarts", "imageParse", 0x272, 16),
    ("p256OrderBe", "scalarFromSlice256", 0x68, 32),
    ("p384OrderBe", "p384VerifyPrehash", 0x30, 48),
    ("sha512IV", "ed25519Verify", 0x1062, 64),
    ("sfs384Empty", "scalarFromSlice384", 0x68, 0),
]

# Data written to the second output instead, so that adding an entry rebuilds
# only the proofs that import it. Same fields as `DATA`.
DATA_EXTRA = [
    ("bsMagic", "bootMainClosure1", 0x56, 4),
    ("bsVersion", "bootMainClosure1", 0x78, 2),
    ("p384CurveA", "p384Decompress", 0x9A, 48),
    ("p384Params", "p384Decompress", 0xD6, 0x9C),
    ("p384SqrtExp", "p384Decompress", 0x166, 48),
    ("p256Params", "p256Decompress", 0xCE, 0x6C),
    ("p256SqrtExp", "p256Decompress", 0x15E, 32),
    ("p256CurveA", "p256FromSec1", 0x39E, 32),
    ("p256B", "p256FromSec1", 0x3C0, 32),
]

# Data for `p384_verify_prehash`, written to the third output. Same fields as
# `DATA`.
DATA_EXTRA2 = [
    ("p384MontOne", "p384VerifyPrehash", 0x1FE, 48),
    ("p384Identity", "p384VerifyPrehash", 0x222, 0x90),
    ("p384G", "p384VerifyPrehash", 0x76E, 0x90),
    ("u12One", "p384VerifyPrehash", 0x650, 48),
    ("p384AffineIdentity", "p384VerifyPrehash", 0x1136, 0x61),
]


# Data for `sigstore::verify`, written to the fourth output. Same fields as
# `DATA`.
DATA_EXTRA3 = [
    ("svConst", "sigstoreVerify", 0x102C, 0x28),
    ("svOidEcdsaSha384", "sigstoreVerify", 0x1B0, 8),
    ("svOidPrime256v1", "sigstoreVerify", 0x2C8, 8),
    ("svOidEcPublicKey", "sigstoreVerify", 0x2DE, 7),
    ("svConstCms", "sigstoreVerify", 0xB5C, 0x30),
    ("svConstExt", "sigstoreVerify", 0x4E8, 0x89),
    ("svNewline", "sigstoreVerify", 0x15F8, 1),
    ("svDash", "sigstoreVerify", 0x1676, 4),
]

# Data for `sha384`, written to the fifth output. Same fields as `DATA`.
DATA_EXTRA4 = [
    ("sha384IV", "sha384Fn", 0x40, 64),
]

# Data for the P-256 check in `p256_verify_prehash`, written to the sixth
# output. Same fields as `DATA`.
DATA_EXTRA5 = [
    ("p256Identity", "p256VerifyPrehash", 0x244, 0x60),
    ("p256InvParams", "p256VerifyPrehash", 0xB26, 0x60),
    ("p256MontOne", "p256VerifyPrehash", 0x220, 0x20),
    ("p256One", "p256VerifyPrehash", 0x39E, 0x20),
    ("p256GMont", "p256VerifyPrehash", 0x6CE, 0x60),
    ("p256AffineIdX", "p256VerifyPrehash", 0x1032, 0x20),
    ("p256OrderLe", "p256VerifyPrehash", 0x354, 0x20),
]

# The Rekor entry's constant pieces in `sigstore::verify`, written to the
# seventh output. Same fields as `DATA`.
DATA_EXTRA6 = [
    ("svRekorLeaf", "sigstoreVerify", 0x18BE, 1),
    ("svRekorPre", "sigstoreVerify", 0x18D4, 0x71),
    ("svRekorMid1", "sigstoreVerify", 0x18FE, 0x1B),
    ("svRekorMid2", "sigstoreVerify", 0x1926, 0x54),
    ("svRekorPost", "sigstoreVerify", 0x194E, 7),
]

# The Ed25519 constants that `ed25519_verify` and `ed25519_public_key_ok`
# read and no earlier output holds, written to the eighth output. Same fields
# as `DATA`.
DATA_EXTRA7 = [
    ("edOrder", "ed25519Verify", 0x4C, 32),
    ("edPrime", "ed25519PublicKeyOk", 0x2A, 32),
    ("edPm1", "ed25519PublicKeyOk", 0x86, 32),
    ("edMontR", "ed25519Verify", 0x148E, 36),
    ("edMontRR", "ed25519Verify", 0x14C2, 36),
    ("edBase", "ed25519Verify", 0x164C, 160),
]

# The keys, the role name, the PEM armor, and the SPKI prefixes that the TUF
# metadata checks in `c3_verify::tuf` compare against, written to the ninth
# output. Same fields as `DATA`.
DATA_EXTRA8 = [
    ("tufPemHeader", "tufPemSpki", 0xE, 0x1B),
    ("tufPemFooter", "tufPemSpki", 0x34, 0x19),
    ("tufExpiresKey", "tufExpires", 0x8, 7),
    ("tufRootKind", "tufParseRoot", 0x12, 4),
    ("tufVersionKey", "tufParseRoot", 0x50, 7),
    ("tufSignaturesKey", "tufParseMetadata", 0xA6, 10),
    ("tufTypeKey", "tufParseMetadata", 0x11C, 5),
    ("tufKeyidKey", "tufParseMetadata", 0x18C, 5),
    ("tufSigKey", "tufParseMetadata", 0x194, 3),
    ("tufRolesKey", "tufRoleKeysRead", 0x46, 5),
    ("tufThresholdKey", "tufRoleKeysRead", 0x7E, 9),
    ("tufKeysKey", "tufRoleKeysRead", 0xC8, 4),
    ("tufKeyidsKey", "tufRoleKeysRead", 0x17A, 6),
    ("tufKeytypeKey", "tufRoleKeysRead", 0x27C, 7),
    ("tufSchemeKey", "tufRoleKeysRead", 0x2C0, 6),
    ("tufKeyvalKey", "tufRoleKeysRead", 0x30E, 6),
    ("tufPublicKey", "tufRoleKeysRead", 0x334, 6),
    ("tufP256Prefix", "tufRoleKeysRead", 0x514, 26),
    ("tufP384Prefix", "tufRoleKeysRead", 0x6BA, 23),
]


# The jump table that `boot_main`'s first closure indexes with a rejection
# code from 0x20 to 0x26, the keys it looks up in `targets.json`, the hex
# digits it writes `trusted_root.json`'s digest in, the keys and values it
# compares in `trusted_root.json` and the bundle's media type, and the
# identity policy, written to the tenth output. Same fields as `DATA`.
DATA_EXTRA9 = [
    ("acRejectTable", "bootMainClosure0", 0x7EA, 28),
    ("acTargetsKeys", "bootMainClosure0", 0x868, 42),
    ("acHexDigits", "bootMainClosure0", 0xB74, 16),
    ("acMediaTypeKey", "bootMainClosure0", 0xC82, 9),
    ("acMediaType", "bootMainClosure0", 0xCC6, 0x39),
    ("acCasKey", "bootMainClosure0", 0xD04, 0x16),
    ("acTlogsKey", "bootMainClosure0", 0xE40, 5),
    ("acPublicKeyKey", "bootMainClosure0", 0xF0E, 9),
    ("acKeyDetailsKey", "bootMainClosure0", 0xF48, 10),
    ("acEd25519Value", "bootMainClosure0", 0xF8C, 12),
    ("acRawBytesKey", "bootMainClosure0", 0xFAC, 8),
    ("acSpkiPrefix", "bootMainClosure0", 0x101A, 12),
    ("acBaseUrlKey", "bootMainClosure0", 0x1056, 7),
    ("acHttps", "bootMainClosure0", 0x10A8, 8),
    ("acSlash", "bootMainClosure0", 0x10EA, 1),
    ("acValidForKey", "bootMainClosure0", 0x1124, 8),
    ("acTsasKey", "bootMainClosure0", 0x11BE, 0x14),
    ("acPolicy", "bootMainClosure0", 0x17C6, 0x23),
]

# The data that the P-256 and P-384 proofs don't read. The data window spans
# the rest, rounded out to 0x20 bytes, and those proofs show that the stack
# stays clear of it.
OUTSIDE_DATA_WINDOW = {"svRekorLeaf", "shaK", "sha512K", "regionEnds", "regionStarts", "acRejectTable",
                       "acTargetsKeys", "acHexDigits", "acMediaTypeKey", "acMediaType", "acCasKey",
                       "acTlogsKey", "acPublicKeyKey", "acKeyDetailsKey", "acEd25519Value", "acRawBytesKey",
                       "acSpkiPrefix", "acBaseUrlKey", "acHttps", "acSlash", "acValidForKey", "acTsasKey",
                       "acPolicy"}


def call_target(code, addr, off):
    """The target of the auipc/jalr pair at `off` of `code`, loaded at `addr`."""
    if off + 8 > len(code):
        sys.exit(f"offset {off:#x} is past the end of the function at {addr:#x}")
    auipc = int.from_bytes(code[off : off + 4], "little")
    jalr = int.from_bytes(code[off + 4 : off + 8], "little")
    rd = (auipc >> 7) & 31
    if auipc & 0x7F != 0x17 or jalr & 0x707F != 0x67 or (jalr >> 15) & 31 != rd:
        sys.exit(f"no auipc/jalr call at offset {off:#x} of the function at {addr:#x}")
    imm = jalr >> 20
    if imm & 0x800:
        imm -= 0x1000
    return (addr + off + (auipc & 0xFFFFF000) + imm) & 0xFFFFFFFE


def lui_addi(code, addr, off):
    """The address that the `lui rd; addi rd, rd` pair at `off` of `code` forms."""
    if off + 8 > len(code):
        sys.exit(f"offset {off:#x} is past the end of the function at {addr:#x}")
    lui = int.from_bytes(code[off : off + 4], "little")
    addi = int.from_bytes(code[off + 4 : off + 8], "little")
    rd = (lui >> 7) & 31
    if (
        lui & 0x7F != 0x37
        or addi & 0x707F != 0x13
        or (addi >> 7) & 31 != rd
        or (addi >> 15) & 31 != rd
    ):
        sys.exit(f"no lui/addi pair at offset {off:#x} of the function at {addr:#x}")
    imm = addi >> 20
    if imm & 0x800:
        imm -= 0x1000
    return ((lui & 0xFFFFF000) + imm) & 0xFFFFFFFF


def shape_hash(code):
    """The SHA-256, in hex, of `code` with the immediates that depend on
    where code and data sit cleared: those of `lui`, `auipc`, `jal`, and
    `c.jal`, and of an instruction right after `lui` or `auipc` that uses
    its result as the base."""
    out = bytearray(code)
    off, base = 0, None
    while off + 2 <= len(code):
        if code[off] & 3 != 3:
            half = int.from_bytes(code[off : off + 2], "little")
            if half & 0xE003 == 0x2001:
                out[off : off + 2] = (half & 0xE003).to_bytes(2, "little")
            off, base = off + 2, None
            continue
        word = int.from_bytes(code[off : off + 4], "little")
        op, rd, rs1 = word & 0x7F, (word >> 7) & 31, (word >> 15) & 31
        if op in (0x37, 0x17, 0x6F):
            word &= 0xFFF
        elif op in (0x67, 0x13, 0x03) and rs1 == base:
            word &= 0xFFFFF
        elif op == 0x23 and rs1 == base:
            word &= 0x1FFF07F
        out[off : off + 4] = word.to_bytes(4, "little")
        base = rd if op in (0x37, 0x17) else None
        off += 4
    return hashlib.sha256(out).hexdigest()


def segments(image):
    count = image[1]
    pos = 24
    out = []
    for _ in range(count):
        addr, length = struct.unpack_from("<II", image, pos)
        out.append((addr, image[pos + 8 : pos + 8 + length]))
        pos += 8 + length
    return out


def bytes_at(segs, addr, size):
    for base, data in segs:
        if base <= addr and addr + size <= base + len(data):
            return data[addr - base : addr - base + size]
    sys.exit(f"no segment holds {size} bytes at {addr:#x}")


def data_addr(entry, extracted):
    name, func, off, size, *rest = entry
    faddr, fcode = extracted[func]
    return lui_addi(fcode, faddr, off) + (rest[0] if rest else 0)


def data_lines(entries, extracted, segs):
    lines = []
    for name, func, off, size, *rest in entries:
        addr = data_addr((name, func, off, size, *rest), extracted)
        delta = rest[0] if rest else 0
        if not size:
            lines += [
                "",
                f"/-- The address `{addr:#x}`, which `{func}` forms at offset {off:#x}. -/",
                f"def {name}Address : Nat := {addr:#x}",
            ]
            continue
        data = bytes_at(segs, addr, size)
        where = f"forms at\noffset {off:#x}" if not delta else f"forms, plus {delta:#x}, at\noffset {off:#x}"
        lines += [
            "",
            f"/-- The {size} bytes at `{addr:#x}` in the image, whose address `{func}` {where}. -/",
            f"def {name}Address : Nat := {addr:#x}",
            "",
            f"def {name}Data : List Nat :=",
            "  [" + ", ".join(f"0x{b:02x}" for b in data) + "]",
        ]
    return lines


def window_lines(extracted):
    """The data window and the read-only window, from where the data sits."""
    spans = [
        (data_addr(e, extracted), e[3], e[0])
        for e in DATA + DATA_EXTRA + DATA_EXTRA2 + DATA_EXTRA3 + DATA_EXTRA4
        + DATA_EXTRA5 + DATA_EXTRA6 + DATA_EXTRA7 + DATA_EXTRA8 + DATA_EXTRA9
    ]
    inside = [(a, n) for a, n, name in spans if name not in OUTSIDE_DATA_WINDOW]
    lo = min(a for a, _ in inside) & ~0x1F
    hi = (max(a + n for a, n in inside) + 0x1F) & ~0x1F
    ro_lo = min(a for a, _, _ in spans) & ~0xFFF
    ro_hi = (max(a + n for a, n, _ in spans) + 0x3FF) & ~0x3FF
    return [
        "",
        "/-- The start of the data window: the data that the P-256 and P-384 proofs",
        "read, rounded out to 0x20 bytes. -/",
        f"def dataWindowAddress : Nat := {lo:#x}",
        "",
        "/-- The data window's size in bytes. -/",
        f"def dataWindowSize : Nat := {hi - lo:#x}",
        "",
        "/-- The start of the read-only window: all the data the proofs name, rounded",
        "down to 0x1000 bytes and up to 0x400. -/",
        f"def roWindowAddress : Nat := {ro_lo:#x}",
        "",
        "/-- The read-only window's size in bytes. -/",
        f"def roWindowSize : Nat := {ro_hi - ro_lo:#x}",
    ]


def name_table(suffix, lines):
    """The `img%` table of the names that `lines` defines as numerals."""
    names = re.findall(r"^def (\w+) : Nat := (0x[0-9a-f]+)$", "\n".join(lines), re.M)
    table = f"imgNames{suffix}"
    return [
        "",
        "set_option maxRecDepth 40000 in",
        "/-- The names above with their values, for `img%`. -/",
        f"def {table} : List (String × Nat) :=",
        "  [" + ",\n   ".join(f'("{n}", {v})' for n, v in names) + "]",
        "",
        "set_option maxRecDepth 40000 in",
        f"theorem {table}_eq : {table} =",
        "    [" + ",\n     ".join(f'("{n}", {n})' for n, _ in names) + "] := rfl",
        "",
        f"macro_rules | `(imgVal% $i) => imgLookup {table} i",
    ]


def main():
    image_path, elf, nm, out, *extra = sys.argv[1:]
    image = open(image_path, "rb").read()
    digest = hashlib.sha256(image).hexdigest()
    symbols = {}
    at = {}
    for line in subprocess.run(
        [nm, "-C", "-S", elf], check=True, capture_output=True, text=True
    ).stdout.splitlines():
        parts = line.split(None, 3)
        if len(parts) == 4 and parts[2] in ("t", "T"):
            entry = (int(parts[0], 16), int(parts[1], 16))
            symbols.setdefault(re.sub(r" \(\.\d+\)$", "", parts[3]), {}).setdefault(entry, parts[3])
            at.setdefault(entry[0], []).append((parts[3], entry[1]))
    for line in subprocess.run(
        [nm, "-S", elf], check=True, capture_output=True, text=True
    ).stdout.splitlines():
        parts = line.split(None, 3)
        if len(parts) == 4 and parts[2] in ("t", "T") and parts[3].startswith("_R"):
            entry = (int(parts[0], 16), int(parts[1], 16))
            symbols.setdefault(parts[3], {}).setdefault(entry, parts[3])
    segs = segments(image)
    lines = [
        "import C3BootProofs.Image.Addr",
        "",
        "/-!",
        "# Bootloader functions",
        "",
        "Generated by `scripts/extract-functions.py` from the bootloader image with",
        f"SHA-256 `{digest}`",
        "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. Each function's bytes",
        "are what the ROM loads at its address.",
        "-/",
        "",
        "namespace C3.Image",
        "",
        f'def imageSha256 : String := "{digest}"',
    ]
    extracted = {}
    lines += function_lines(FUNCTIONS, extracted, symbols, at, segs)
    lines += data_lines(DATA, extracted, segs)
    lines += window_lines(extracted)
    lines += name_table("", lines)
    lines += ["", "end C3.Image", ""]
    with open(out, "w") as f:
        f.write("\n".join(lines))
    write_extra(extra, digest, extracted, symbols, at, segs)


def function_lines(functions, extracted, symbols, at, segs):
    """The definitions of `functions`' addresses and code, which it also
    records in `extracted`."""
    lines = []
    for name, source, *shape in functions:
        if isinstance(source, tuple):
            caller, off = source
            caddr, ccode = extracted[caller]
            addr = call_target(ccode, caddr, off)
            found = [s for s in at.get(addr, []) if s[1] > 0]
            if len(found) != 1:
                sys.exit(f"the call at {caller}+{off:#x} reaches {addr:#x}, which starts {found}")
            symbol, size = found[0]
            what = f"`{symbol}`, which `{caller}` calls at offset {off:#x},"
        else:
            if source not in symbols:
                sys.exit(f"no symbol {source}")
            found = symbols[source]
            match = list(found)
            if shape or len(match) > 1:
                hashes = {e: shape_hash(bytes_at(segs, *e)) for e in found}
                match = [e for e in found if shape and hashes[e].startswith(shape[0])]
            if len(match) != 1:
                listing = ", ".join(f"{a:#x} ({hashes[(a, n)][:12]})" for a, n in sorted(found))
                sys.exit(f"{name}: {len(match)} of the functions named {source} match: {listing}")
            addr, size = match[0]
            symbol = found[match[0]]
            what = f"`{symbol}`,"
            if size == 0:
                size = min(a for a, s in at.items() if a > addr and any(n > 0 for _, n in s)) - addr
                what = f"`{symbol}`, up to the next function,"
        code = bytes_at(segs, addr, size)
        extracted[name] = (addr, code)
        rows = [
            "    " + ", ".join(f"0x{b:02x}" for b in code[i : i + 12])
            for i in range(0, len(code), 12)
        ]
        lines += [
            "",
            f"/-- {what} at `{addr:#x}` in the image. -/",
            f"def {name}Address : Nat := {addr:#x}",
            "",
            *(["set_option maxRecDepth 40000 in"] if len(code) > 2048 else []),
            f"def {name}Code : List Nat :=",
            "  [" + ",\n".join(rows).lstrip() + "]",
        ]
    return lines


def write_extra(extra, digest, extracted, symbols, at, segs):
    """Writes the outputs after the first."""
    if extra:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader data",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. Data that later",
            "proofs read, kept out of `Bootloader.lean` so that adding an entry rebuilds",
            "only the proofs that import this file.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += data_lines(DATA_EXTRA, extracted, segs)
        more += name_table("Data", more)
        more += ["", "end C3.Image", ""]
        with open(extra[0], "w") as f:
            f.write("\n".join(more))
    if len(extra) > 1:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader data for `p384_verify_prehash`",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. The constants",
            "`p384_verify_prehash` reads that no earlier proof does.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += data_lines(DATA_EXTRA2, extracted, segs)
        more += name_table("Data2", more)
        more += ["", "end C3.Image", ""]
        with open(extra[1], "w") as f:
            f.write("\n".join(more))
    if len(extra) > 2:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader data for `sigstore::verify`",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. The OIDs, the tables",
            "of OIDs, and the strings that `sigstore::verify` reads.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += data_lines(DATA_EXTRA3, extracted, segs)
        more += name_table("Data3", more)
        more += ["", "end C3.Image", ""]
        with open(extra[2], "w") as f:
            f.write("\n".join(more))
    if len(extra) > 3:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader data for `sha384`",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. SHA-384's initial",
            "hash value.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += data_lines(DATA_EXTRA4, extracted, segs)
        more += name_table("Data4", more)
        more += ["", "end C3.Image", ""]
        with open(extra[3], "w") as f:
            f.write("\n".join(more))
    if len(extra) > 4:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader data for `p256_verify_prehash`",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. The point at",
            "infinity that the main loop of the P-256 check starts from, the field's",
            "constants that the inversion of the sum's `Z` copies, and the group order",
            "in little-endian order.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += data_lines(DATA_EXTRA5, extracted, segs)
        more += name_table("Data5", more)
        more += ["", "end C3.Image", ""]
        with open(extra[4], "w") as f:
            f.write("\n".join(more))
    if len(extra) > 5:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader data for the Rekor entry in `sigstore::verify`",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. The leaf hash's",
            "prefix byte and the JSON around the digest, the signature, and the",
            "certificate in the Rekor entry that `sigstore::verify` hashes.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += data_lines(DATA_EXTRA6, extracted, segs)
        more += name_table("Data6", more)
        more += ["", "end C3.Image", ""]
        with open(extra[5], "w") as f:
            f.write("\n".join(more))
    if len(extra) > 6:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader data for the Ed25519 check",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. The group order `L`,",
            "the field prime `p` and `p - 1` as 32 bytes, the Montgomery constants",
            "`2^261 mod L` and `2^522 mod L`, and the base point that `ed25519_verify`",
            "and `ed25519_public_key_ok` read.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += data_lines(DATA_EXTRA7, extracted, segs)
        more += name_table("Data7", more)
        more += ["", "end C3.Image", ""]
        with open(extra[6], "w") as f:
            f.write("\n".join(more))
    if len(extra) > 7:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader data for the TUF metadata checks",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. The PEM armor that",
            "`pem_spki` strips, the role name that `parse_root` passes, the keys that",
            "`parse_metadata`, `parse_root`, `expires`, and `RoleKeys::read` look up,",
            "and the SPKI prefixes that `decode_key` strips.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += data_lines(DATA_EXTRA8, extracted, segs)
        more += name_table("Data8", more)
        more += ["", "end C3.Image", ""]
        with open(extra[7], "w") as f:
            f.write("\n".join(more))
    if len(extra) > 8:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader data for `boot_main`'s first closure",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. The jump table that",
            "the closure's rejection log indexes, the keys and values it compares, and",
            "the identity policy.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += data_lines(DATA_EXTRA9, extracted, segs)
        more += name_table("Data9", more)
        more += ["", "end C3.Image", ""]
        with open(extra[8], "w") as f:
            f.write("\n".join(more))
    if len(extra) > 9:
        more = [
            "import C3BootProofs.Image.Bootloader",
            "",
            "/-!",
            "# Bootloader functions that run before `boot_main`",
            "",
            "Generated by `scripts/extract-functions.py` from the bootloader image with",
            f"SHA-256 `{digest}`",
            "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. `_start`, which the",
            "ROM jumps to, `setup`, and the watchdog and clock setup that `setup` calls.",
            "-/",
            "",
            "namespace C3.Image",
        ]
        more += function_lines(FUNCTIONS_RESET, extracted, symbols, at, segs)
        more += name_table("Reset", more)
        more += ["", "end C3.Image", ""]
        with open(extra[9], "w") as f:
            f.write("\n".join(more))


if __name__ == "__main__":
    main()
