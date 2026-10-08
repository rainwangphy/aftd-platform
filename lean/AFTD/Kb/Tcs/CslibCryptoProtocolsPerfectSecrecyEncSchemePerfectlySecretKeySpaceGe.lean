import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePerfectlySecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyShannonKeySpace
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge

Topic: cryptography   Node: e0caff5fa257

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Basic.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Perfect secrecy requires `|K| ≥ |M|` ([KatzLindell2020], Theorem 2.12).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {M K C : Type u} in
/-- Perfect secrecy requires `|K| ≥ |M|` ([KatzLindell2020], Theorem 2.12). -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge [Finite K]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret) :
    Nat.card K ≥ Nat.card M :=
  PerfectSecrecy.shannonKeySpace scheme h
