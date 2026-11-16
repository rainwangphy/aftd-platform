import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370FinsetNeCompl

/-!
# op1370_reciprocal_update_additive

Topic: combinatorics   Node: 752771d3df74

Provenance: helper lemma.

A reciprocal pair replacement equals an additive update at the set and its complement.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_reciprocal_update_additive
    {α K : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field K]
    (q : Finset α → K) (hrec : ∀ X, q X * q Xᶜ = 1)
    (Y : Finset α) (u t : K) (hu : u ≠ 0) (hq : q Y = u) :
    (fun X => if X = Y then u + t else if X = Yᶜ then (u + t)⁻¹ else q X) =
    (fun X => (q X + if X = Y then t else 0) +
      if X = Yᶜ then (u + t)⁻¹ - u⁻¹ else 0) := by
  classical
  have hne : Y ≠ Yᶜ := op1370_finset_ne_compl Y
  have hqc : q Yᶜ = u⁻¹ := by
    have h := hrec Y
    rw [hq] at h
    have hh : u * q Yᶜ = u * u⁻¹ := by simpa [hu] using h
    exact (mul_left_cancel₀ hu) hh
  funext X
  by_cases hX : X = Y
  · subst X
    simp [hne, hq]
  · by_cases hXc : X = Yᶜ
    · subst X
      simp [Ne.symm hne, hqc]
    · simp [hX, hXc]
