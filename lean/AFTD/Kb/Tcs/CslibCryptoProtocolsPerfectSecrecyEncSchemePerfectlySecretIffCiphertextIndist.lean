import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePerfectlySecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextIndist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyCiphertextIndistOfPerfectlySecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyPerfectlySecretOfCiphertextIndist
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_iff_ciphertextIndist

Topic: cryptography   Node: 0cfe24ab6993

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_iff_ciphertextIndist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Basic.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A scheme is perfectly secret iff the ciphertext distribution is independent of the plaintext ([KatzLindell2020], Lemma 2.5).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {M K C : Type u} in
/-- A scheme is perfectly secret iff the ciphertext distribution is independent of the plaintext ([KatzLindell2020], Lemma 2.5). -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_iff_ciphertextIndist (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔ scheme.CiphertextIndist :=
  ⟨PerfectSecrecy.ciphertextIndist_of_perfectlySecret scheme,
   PerfectSecrecy.perfectlySecret_of_ciphertextIndist scheme⟩
