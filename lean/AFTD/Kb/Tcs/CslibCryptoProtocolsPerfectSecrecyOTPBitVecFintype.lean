import AFTD.Prelude

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.OTP.bitVecFintype

Topic: cryptography   Node: 63ad2cd28839

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.OTP.bitVecFintype`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/OneTimePad.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.PerfectSecrecy.OTP.bitVecFintype
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Crypto.Protocols.PerfectSecrecy.OTP.bitVecFintype (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2 ^ n))
    ⟨BitVec.ofFin, BitVec.toFin, fun x => by simp, fun x => by simp⟩

-- TODO: upstream to Mathlib — general BitVec XOR cancellation lemma.
