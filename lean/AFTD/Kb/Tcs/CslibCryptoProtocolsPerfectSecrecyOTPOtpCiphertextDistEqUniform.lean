import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyOTPBitVecFintype
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyOTPEqXorIffXorEq

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.OTP.otp_ciphertextDist_eq_uniform

Topic: cryptography   Node: d9cb6b8734e3

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.OTP.otp_ciphertextDist_eq_uniform`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/OneTimePad.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The ciphertext distribution of the OTP is uniform, regardless of the message.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The ciphertext distribution of the OTP is uniform, regardless of the message. -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.OTP.otp_ciphertextDist_eq_uniform (l : ℕ) (m : BitVec l) :
    (PMF.uniformOfFintype (BitVec l)).bind
      (fun k => PMF.pure (k ^^^ m)) =
    PMF.uniformOfFintype (BitVec l) := by simp [PMF.ext_iff, eq_xor_iff_xor_eq]
