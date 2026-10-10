import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapInstMonoid
import AFTD.Kb.Physics.LinearPMapIsSymmetricDef

/-!
# LinearPMap.IsSymmetric.isSelfAdjoint_of_range_eq_top

Topic: quantum_mechanics   Node: c9cdb65f7657

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.isSelfAdjoint_of_range_eq_top`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Self-adjointness from surjectivity of `T ± i`: a symmetric, densely-defined operator `T` for which `T + I • 1` and `T - I • 1` both have full range is self-adjoint.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
open InnerProductSpace in
open Complex ComplexConjugate in
variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
  {α : Type*} [Fintype α]
  {T T₁ T₂ : H →ₗ.[ℂ] H} {S : α → H →ₗ.[ℂ] H}
  {U U₁ U₂ : H →ₗ.[ℂ] H'} {W : α → H →ₗ.[ℂ] H'}
  {V V₁ V₂ : H' →ₗ.[ℂ] H''} in
variable (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H) in
variable {u A} in
/-- Self-adjointness from surjectivity of `T ± i`: a symmetric, densely-defined operator `T` for which `T + I • 1` and `T - I • 1` both have full range is self-adjoint. -/
lemma LinearPMap.IsSymmetric.isSelfAdjoint_of_range_eq_top [CompleteSpace H] (hsym : T.IsSymmetric)
    (hdense : T.HasDenseDomain)
    (hadd : (T + I • 1).toFun.range = ⊤) (hsub : (T - I • 1).toFun.range = ⊤) :
    IsSelfAdjoint T := by
  have hplus : ∀ φ : H, ∃ ψ : T.domain, T ψ + I • (ψ : H) = φ := fun φ => by
    obtain ⟨ψ, hψ⟩ := LinearMap.range_eq_top.mp hadd φ
    exact ⟨⟨(ψ : H), (Submodule.mem_inf.mp ψ.2).1⟩, hψ⟩
  have hminus : ∀ φ : H, ∃ ψ : T.domain, T ψ - I • (ψ : H) = φ := fun φ => by
    obtain ⟨ψ, hψ⟩ := LinearMap.range_eq_top.mp hsub φ
    exact ⟨⟨(ψ : H), (Submodule.mem_inf.mp ψ.2).1⟩, hψ⟩
  rw [isSelfAdjoint_def]
  have hle : T ≤ T.adjoint := (isSymmetric_def.mp hsym).le_adjoint hdense
  apply le_antisymm _ hle
  apply le_of_eqLocus_ge
  intro w hw
  let W : T.adjoint.domain := ⟨w, hw⟩
  obtain ⟨x, hx⟩ := hminus (T.adjoint W - I • (W : H))
  set X : T.adjoint.domain := ⟨x, hle.1 x.2⟩ with hX
  have hxeq : T.adjoint X = T x := (hle.2 (x := x) (y := X) rfl).symm
  have hdiff : T.adjoint (W - X) = I • ((W - X) : H) := by
    rw [LinearPMap.map_sub, hxeq, hX, Subtype.coe_mk, smul_sub, sub_eq_sub_iff_sub_eq_sub, hx]
  have hker : ∀ w : T.adjoint.domain, T.adjoint w = I • (w : H) → (w : H) = 0 := by
    intro w hw
    obtain ⟨v, hv⟩ := hplus (w : H)
    suffices ⟪↑w, T v + I • v⟫_ℂ = 0 by
      exact inner_self_eq_zero.mp (hv ▸ this)
    rw [inner_add_right, inner_smul_right, ← adjoint_isFormalAdjoint hdense w v, hw,
      inner_smul_left, conj_I]
    ring
  obtain rfl : w = (x : H) := sub_eq_zero.mp (hker (W - X) hdiff)
  exact ⟨hw, x.2, hxeq⟩
