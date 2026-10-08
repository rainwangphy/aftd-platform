import AFTD.Prelude

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.OTP.eq_xor_iff_xor_eq

Topic: cryptography   Node: b1954355363d

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.OTP.eq_xor_iff_xor_eq`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/OneTimePad.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

XOR by a fixed mask is self-inverse on `BitVec`: `c = k ^^^ m ↔ c ^^^ m = k`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- XOR by a fixed mask is self-inverse on `BitVec`: `c = k ^^^ m ↔ c ^^^ m = k`. -/
lemma Cslib.Crypto.Protocols.PerfectSecrecy.OTP.eq_xor_iff_xor_eq {l : ℕ} (c m k : BitVec l) :
    (c = k ^^^ m) ↔ (c ^^^ m = k) := by grind
