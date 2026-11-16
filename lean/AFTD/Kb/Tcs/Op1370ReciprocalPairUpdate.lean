import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370FinsetNeCompl

/-!
# op1370_reciprocal_pair_update

Topic: combinatorics   Node: 58ac9c39e68d

Provenance: helper lemma.

Replacing a nonzero weight and its complementary weight by reciprocal values preserves the reciprocal condition.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_reciprocal_pair_update
    {α K : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field K]
    (q : Finset α → K) (hrec : ∀ X, q X * q Xᶜ = 1)
    (Y : Finset α) (u : K) (hu : u ≠ 0) :
    let q' : Finset α → K := fun X => if X = Y then u else if X = Yᶜ then u⁻¹ else q X
    ∀ X, q' X * q' Xᶜ = 1 := by
  classical
  have hne : Y ≠ Yᶜ := op1370_finset_ne_compl Y
  dsimp only
  intro X
  by_cases hX : X = Y
  · subst X
    simp [hne, Ne.symm hne, hu]
  · by_cases hXc : X = Yᶜ
    · subst X
      simp [hne, Ne.symm hne, hu, mul_comm]
    · have hc1 : Xᶜ ≠ Y := by
        intro h
        apply hXc
        have hh := congrArg (fun T : Finset α => Tᶜ) h
        simpa using hh
      have hc2 : Xᶜ ≠ Yᶜ := by
        intro h
        apply hX
        have hh := congrArg (fun T : Finset α => Tᶜ) h
        simpa using hh
      simpa [hX, hXc, hc1, hc2] using hrec X
