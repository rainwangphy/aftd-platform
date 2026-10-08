import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ciphertextDist

Topic: cryptography   Node: 0a13b39ee21c

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ciphertextDist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The distribution of `Enc_K(m)` when `K ← Gen`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {M K C : Type u} in
/-- The distribution of `Enc_K(m)` when `K ← Gen`. -/
noncomputable def Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ciphertextDist (scheme : EncScheme M K C) (m : M) : PMF C := do
  scheme.enc (← scheme.gen) m
