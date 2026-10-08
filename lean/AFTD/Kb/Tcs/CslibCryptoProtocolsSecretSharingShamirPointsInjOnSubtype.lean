import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.points_injOn_subtype

Topic: cryptography   Node: 98c95b6d9bc0

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.points_injOn_subtype`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.points_injOn_subtype
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.points_injOn_subtype {F Party : Type*} [Field F] [Fintype Party]
    (params : Params F Party) (s : Finset Party) :
    Set.InjOn (fun i : s => params.point i) (s.attach : Finset s) := by
  intro i _ j _ hij
  apply Subtype.ext
  exact params.point_injective hij
