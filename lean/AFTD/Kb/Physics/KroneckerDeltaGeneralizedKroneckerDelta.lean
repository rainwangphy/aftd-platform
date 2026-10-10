import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta

/-!
# KroneckerDelta.generalizedKroneckerDelta

Topic: classical_mechanics   Node: 2131fb69a156

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.generalizedKroneckerDelta`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Generalized Kronecker delta: `δ^{μ₁...μₙ}_{ν₁...νₙ} = det (δ[μᵢ, νⱼ])`. This is defined for any finite type `α` with decidable equality.
-/

set_option quotPrecheck false
open KroneckerDelta
local notation "δℤ" => (fun ρ σ => ((kroneckerDelta ρ σ : ℕ) : ℤ))

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {α M : Type*} [DecidableEq α] in
open Matrix in
/-- Generalized Kronecker delta: `δ^{μ₁...μₙ}_{ν₁...νₙ} = det (δ[μᵢ, νⱼ])`. This is defined for any finite type `α` with decidable equality. -/
def KroneckerDelta.generalizedKroneckerDelta {α ι : Type} [DecidableEq α]
    [DecidableEq ι] [Fintype ι]
    (μ : ι → α) (ν : ι → α) : ℤ :=
  Matrix.det (fun i j => δℤ (μ i) (ν j))
