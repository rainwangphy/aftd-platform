import AFTD.Prelude

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Params

Topic: cryptography   Node: 9cc3826097c1

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Params`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Public parameters for a finite Shamir secret-sharing instance. The threshold is bundled with the evaluation points so the API can enforce the standard non-vacuous `threshold < number of parties` side condition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- Public parameters for a finite Shamir secret-sharing instance. The threshold is bundled with the evaluation points so the API can enforce the standard non-vacuous `threshold < number of parties` side condition. -/
structure Cslib.Crypto.Protocols.SecretSharing.Shamir.Params (F : Type*) [Zero F] (Party : Type*) [Fintype Party] where
  /-- A coalition of size `threshold + 1` is the first authorized size. -/
  threshold : ℕ
  /-- Standard Shamir sharing requires `threshold < number of parties`. -/
  threshold_lt_card : threshold < Fintype.card Party
  /-- The public evaluation point assigned to each party. -/
  point : Party → F
  /-- Distinct parties receive distinct evaluation points. -/
  point_injective : Function.Injective point
  /-- Standard Shamir sharing forbids the point `0`, which would reveal the
  secret directly. -/
  point_nonzero : ∀ i : Party, point i ≠ 0
