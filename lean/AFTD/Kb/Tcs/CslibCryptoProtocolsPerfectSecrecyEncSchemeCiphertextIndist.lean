import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextDist

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.CiphertextIndist

Topic: cryptography   Node: 150a0188bae8

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.CiphertextIndist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ciphertext indistinguishability: the ciphertext distribution is the same for all messages ([KatzLindell2020], Lemma 2.5).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {M K C : Type u} in
/-- Ciphertext indistinguishability: the ciphertext distribution is the same for all messages ([KatzLindell2020], Lemma 2.5). -/
def Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.CiphertextIndist (scheme : EncScheme M K C) : Prop :=
  ∀ m₀ m₁ : M, scheme.ciphertextDist m₀ = scheme.ciphertextDist m₁
