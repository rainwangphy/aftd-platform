import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialReconstruct

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct

Topic: cryptography   Node: f63c11a0c3dc

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reconstruct the secret from one coalition's Shamir shares.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- Reconstruct the secret from one coalition's Shamir shares. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct (params : Params F Party)
    (s : Finset Party) (σ : s → F) : F :=
  Polynomial.reconstruct (fun i : s => params.point i) σ
