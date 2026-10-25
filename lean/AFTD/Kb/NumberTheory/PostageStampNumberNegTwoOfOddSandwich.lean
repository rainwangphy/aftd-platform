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
  have hbdd : BddAbove {n | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧
      postage_stamp_basis_range h A = n} := by
    refine ⟨(h ^ 2 + 6 * h + 1) / 4, ?_⟩
    rintro n ⟨A, hA, hneg, rfl⟩
    have := hup A hA hneg; omega
  have hmem : postage_stamp_basis_range h A0 ∈ {n | ∃ A : Finset ℤ, A.card = 2 + 1 ∧
      (∃ a ∈ A, a < 0) ∧ postage_stamp_basis_range h A = n} := ⟨A0, hA0, hneg0, rfl⟩
  have hle := csSup_le ⟨_, hmem⟩ (fun n hn => show n ≤ (h ^ 2 + 6 * h + 1) / 4 - gap by
    obtain ⟨A, hA, hneg, rfl⟩ := hn
    have := hup A hA hneg; omega)
  have hge := le_csSup hbdd hmem
  have h0 := hup A0 hA0 hneg0
  unfold postage_stamp_number_neg
  omega
