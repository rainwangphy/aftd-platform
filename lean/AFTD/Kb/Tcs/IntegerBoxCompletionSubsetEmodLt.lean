import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# integer_box_completion_subset_emod_lt

Topic: combinatorics   Node: 8c5fccd70047

Provenance: helper lemma. Supporting lemmas for OP-259, arXiv:2610.19965 Question 3.1, deep session IN-185. This is the restricted full-box completion route; no claim that an arbitrary long bad sequence contains such a box.

If every subset completed by an integer vector in the box [0,n-1]^r that vanishes modulo n also vanishes modulo n squared, each negative subset-sum coordinate has residue below n modulo n squared.
-/

theorem integer_box_completion_subset_emod_lt {ι : Type*} [DecidableEq ι]
    (n r : ℕ) (hn : 1 < n) (a : ι → Fin r → ℤ)
    (hbad : ∀ s : Finset ι, ∀ c : Fin r → ℤ,
      (∀ j, 0 ≤ c j ∧ c j < n) →
      (∀ j, (n : ℤ) ∣ c j + ∑ i ∈ s, a i j) →
      ∀ j, (n : ℤ) ^ 2 ∣ c j + ∑ i ∈ s, a i j) :
    ∀ s : Finset ι, ∀ j, (-∑ i ∈ s, a i j) % (n : ℤ) ^ 2 < n := by
  intro s j
  let c : Fin r → ℤ := fun j => (-∑ i ∈ s, a i j) % n
  have hnz : (1 : ℤ) < n := by exact_mod_cast hn
  have hc : ∀ j, 0 ≤ c j ∧ c j < n := by
    intro j
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hd : ∀ j, (n : ℤ) ∣ c j + ∑ i ∈ s, a i j := by
    intro j
    have h := (Int.mod_modEq (-∑ i ∈ s, a i j) (n : ℤ)).symm.dvd
    simpa [c, sub_neg_eq_add] using h
  have hd2 := hbad s c hc hd j
  have he : (-∑ i ∈ s, a i j) % (n : ℤ) ^ 2 = c j := by
    have hm : (-∑ i ∈ s, a i j) ≡ c j [ZMOD (n : ℤ) ^ 2] :=
      Int.modEq_iff_dvd.mpr (by simpa [sub_neg_eq_add] using hd2)
    exact hm.eq.trans (Int.emod_eq_of_lt (hc j).1 (by have := (hc j).2; nlinarith))
  rw [he]
  exact (hc j).2
