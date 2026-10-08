import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextDist

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.jointDist

Topic: cryptography   Node: 5f8475581a98

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.jointDist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Joint distribution of `(M, C)` given a message prior.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {M K C : Type u} in
/-- Joint distribution of `(M, C)` given a message prior. -/
noncomputable def Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.jointDist (scheme : EncScheme M K C) (msgDist : PMF M) : PMF (M × C) := do
  let m ← msgDist
  return (m, ← scheme.ciphertextDist m)
