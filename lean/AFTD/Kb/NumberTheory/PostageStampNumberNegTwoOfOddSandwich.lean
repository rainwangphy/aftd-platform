import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.PostageStampNumberNeg

/-!
# postage_stamp_number_neg_two_of_odd_sandwich

Topic: elementary_number_theory   Node: c8e11b73ff3e

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

If every 3-set with a negative element has h-range ≤ n_h(2) - g and one such set reaches n_h(2) - g, then n♭_h(2) + g = n_h(2).
-/

theorem postage_stamp_number_neg_two_of_odd_sandwich (h gap : ℕ)
    (hup : ∀ A : Finset ℤ, A.card = 3 → (∃ a ∈ A, a < 0) →
      postage_stamp_basis_range h A + gap ≤ (h ^ 2 + 6 * h + 1) / 4)
    (A0 : Finset ℤ) (hA0 : A0.card = 3) (hneg0 : ∃ a ∈ A0, a < 0)
    (hlow : (h ^ 2 + 6 * h + 1) / 4 ≤ postage_stamp_basis_range h A0 + gap) :
    postage_stamp_number_neg h 2 + gap = (h ^ 2 + 6 * h + 1) / 4 := by
  classical
  -- The sandwich hypothesis at `A0` pins the value: `n_h(A0) + gap` is exactly `n_h(2)`.
  have hA0eq : postage_stamp_basis_range h A0 + gap = (h ^ 2 + 6 * h + 1) / 4 :=
    le_antisymm (hup A0 hA0 hneg0) hlow
  -- Every 3-set with a negative element has range at most that of `A0`.
  have hle : ∀ (A : Finset ℤ), A.card = 3 → (∃ a ∈ A, a < 0) →
      postage_stamp_basis_range h A ≤ postage_stamp_basis_range h A0 := by
    intro A hA hneg
    have := hup A hA hneg
    omega
  -- Hence the defining set of `n♭_h(2)` is bounded by `n_h(A0)`, and contains it.
  have hbdd : BddAbove {n : ℕ | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧
      postage_stamp_basis_range h A = n} := by
    refine ⟨postage_stamp_basis_range h A0, ?_⟩
    rintro n ⟨A, hA, hneg, rfl⟩
    exact hle A hA hneg
  have hmem : postage_stamp_basis_range h A0 ∈ {n : ℕ | ∃ A : Finset ℤ, A.card = 2 + 1 ∧
      (∃ a ∈ A, a < 0) ∧ postage_stamp_basis_range h A = n} :=
    ⟨A0, hA0, hneg0, rfl⟩
  have hsup : postage_stamp_number_neg h 2 = postage_stamp_basis_range h A0 := by
    unfold postage_stamp_number_neg
    exact le_antisymm
      (csSup_le ⟨_, hmem⟩ (by rintro n ⟨A, hA, hneg, rfl⟩; exact hle A hA hneg))
      (le_csSup hbdd hmem)
  rw [hsup]
  exact hA0eq
