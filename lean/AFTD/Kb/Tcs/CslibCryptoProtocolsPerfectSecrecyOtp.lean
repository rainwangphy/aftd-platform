import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeOfPure
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyOTPBitVecFintype

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.otp

Topic: cryptography   Node: 85283bd78957

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.otp`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/OneTimePad.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The one-time pad over `l`-bit strings. Encryption and decryption are XOR ([KatzLindell2020], Construction 2.9).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The one-time pad over `l`-bit strings. Encryption and decryption are XOR ([KatzLindell2020], Construction 2.9). -/
noncomputable def Cslib.Crypto.Protocols.PerfectSecrecy.otp (l : ℕ) :
    EncScheme (BitVec l) (BitVec l) (BitVec l) :=
  .ofPure (PMF.uniformOfFintype _) (· ^^^ ·) (· ^^^ ·) fun k m => by
    simp [← BitVec.xor_assoc]
