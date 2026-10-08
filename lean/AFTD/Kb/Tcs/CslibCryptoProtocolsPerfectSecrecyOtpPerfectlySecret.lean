import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePerfectlySecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyOtp
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextIndist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePerfectlySecretIffCiphertextIndist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyOTPBitVecFintype
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeOfPure
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyOTPOtpCiphertextDistEqUniform
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.otp_perfectlySecret

Topic: cryptography   Node: 2df90b2326bc

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.otp_perfectlySecret`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/OneTimePad.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10). -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.otp_perfectlySecret (l : ℕ) : (otp l).PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr fun m₀ m₁ => by
    simp only [EncScheme.ciphertextDist, otp]
    exact (OTP.otp_ciphertextDist_eq_uniform l m₀).trans
      (OTP.otp_ciphertextDist_eq_uniform l m₁).symm
