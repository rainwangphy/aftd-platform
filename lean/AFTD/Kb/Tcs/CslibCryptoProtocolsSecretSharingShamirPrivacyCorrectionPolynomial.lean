import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial

Topic: cryptography   Node: f540d8370dea

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial
    (params : Params F Party) (s : Finset Party)
    (secret₀ secret₁ : F) : _root_.Polynomial F :=
  by
    classical
    exact _root_.Lagrange.interpolate s.attach (fun i : s => params.point i)
      (fun i : s => (secret₀ - secret₁) / params.point i)
