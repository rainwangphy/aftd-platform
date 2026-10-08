import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.authorized

Topic: cryptography   Node: 45c203f02185

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.authorized`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A coalition is authorized exactly when it contains at least `params.threshold + 1` parties.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- A coalition is authorized exactly when it contains at least `params.threshold + 1` parties. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.authorized (params : Params F Party) (s : Finset Party) : Prop :=
  params.threshold + 1 ≤ s.card
