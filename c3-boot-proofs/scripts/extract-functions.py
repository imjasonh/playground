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

Usage: extract-functions.py ESP_IMAGE ELF NM OUT
"""

import hashlib
import struct
import subprocess
import sys

# Lean name, then the demangled symbol, the mangled one when two functions
# demangle alike, or the Lean name of an earlier function and the offset of a
# call in it.
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
    ("selectI64", "<ctutils::choice::Choice>::select_i64 (.170)"),
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
    ("u32Min", "crypto_bigint::primitives::u32_min (.169)"),
    ("sliceReverse", "<[u8]>::reverse"),
    ("uintRefIsZero", "<crypto_bigint::uint::ref_type::UintRef>::is_zero"),
    ("choiceNot", "<subtle::Choice as core::ops::bit::Not>::not (.164)"),
    ("splitAt12", "<crypto_bigint::uint::ref_type::UintRef>::split_at (.238)"),
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
    ("splitAt8", "<crypto_bigint::uint::ref_type::UintRef>::split_at (.165)"),
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
]

# Lean name, then the Lean name of an extracted function, the offset of a
# `lui; addi` pair in it that forms an address, the data's size, and,
# optionally, the data's offset from that address.
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
]


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


def main():
    image_path, elf, nm, out = sys.argv[1:]
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
            symbols.setdefault(parts[3], []).append(entry)
            at.setdefault(entry[0], []).append((parts[3], entry[1]))
    for line in subprocess.run(
        [nm, "-S", elf], check=True, capture_output=True, text=True
    ).stdout.splitlines():
        parts = line.split(None, 3)
        if len(parts) == 4 and parts[2] in ("t", "T") and parts[3].startswith("_R"):
            symbols.setdefault(parts[3], []).append((int(parts[0], 16), int(parts[1], 16)))
    segs = segments(image)
    lines = [
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
    for name, source in FUNCTIONS:
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
            symbol = source
            if symbol not in symbols:
                sys.exit(f"no symbol {symbol}")
            if len(set(symbols[symbol])) != 1:
                sys.exit(f"{symbol} names more than one function: {symbols[symbol]}")
            addr, size = symbols[symbol][0]
            what = f"`{symbol}`,"
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
    for name, func, off, size, *rest in DATA:
        faddr, fcode = extracted[func]
        base = lui_addi(fcode, faddr, off)
        delta = rest[0] if rest else 0
        addr = base + delta
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
    lines += ["", "end C3.Image", ""]
    with open(out, "w") as f:
        f.write("\n".join(lines))


if __name__ == "__main__":
    main()
