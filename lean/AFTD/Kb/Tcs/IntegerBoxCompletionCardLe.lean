import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteArrayCardLeOfSubsetSquareModLt
import AFTD.Kb.Tcs.IntegerBoxCompletionSubsetEmodLt

/-!
# integer_box_completion_card_le

Topic: combinatorics   Node: e414061958fd

Provenance: helper lemma. Supporting lemmas for OP-259, arXiv:2610.19965 Question 3.1, deep session IN-185. This is the restricted full-box completion route; no claim that an arbitrary long bad sequence contains such a box.

An admissible integer vector family with the full-box completion property has at most r(n-1) terms.
-/

theorem integer_box_completion_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n r : ℕ) (hn : 1 < n) (a : ι → Fin r → ℤ)
    (ha : ∀ i, ∃ j, ¬ (n : ℤ) ∣ a i j)
    (hbad : ∀ s : Finset ι, ∀ c : Fin r → ℤ,
      (∀ j, 0 ≤ c j ∧ c j < n) →
      (∀ j, (n : ℤ) ∣ c j + ∑ i ∈ s, a i j) →
      ∀ j, (n : ℤ) ^ 2 ∣ c j + ∑ i ∈ s, a i j) :
    Fintype.card ι ≤ r * (n - 1) := by
  let v : ι → Fin r → ℕ := fun i j => ((-a i j) % (n : ℤ) ^ 2).toNat
  have hnz : (1 : ℤ) < n := by exact_mod_cast hn
  have hcanon : ∀ i j, (v i j : ℤ) = (-a i j) % (n : ℤ) ^ 2 := by
    intro i j
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  have hsmall : ∀ i j, v i j < n := by
    intro i j
    have h := integer_box_completion_subset_emod_lt n r hn a hbad {i} j
    simp only [Finset.sum_singleton] at h
    rw [← hcanon i j] at h
    exact_mod_cast h
  have hpos : ∀ i, 0 < ∑ j, v i j := by
    intro i
    obtain ⟨j, hj⟩ := ha i
    have hv : 0 < v i j := by
      by_contra h
      have hz : v i j = 0 := by omega
      have hem : (-a i j) % (n : ℤ) ^ 2 = 0 := by simpa [hz] using (hcanon i j).symm
      have hd : (n : ℤ) ^ 2 ∣ -a i j := Int.dvd_of_emod_eq_zero hem
      have hdn : (n : ℤ) ∣ (n : ℤ) ^ 2 := by simpa [pow_two] using (dvd_mul_right (n : ℤ) (n : ℤ))
      exact hj (by simpa using dvd_neg.mpr (dvd_trans hdn hd))
    exact lt_of_lt_of_le hv (Finset.single_le_sum (fun j _ => Nat.zero_le (v i j)) (Finset.mem_univ j))
  apply finite_array_card_le_of_subset_square_mod_lt n r hn v hsmall hpos
  intro s j
  have he : (∑ i ∈ s, (v i j : ℤ)) % (n : ℤ) ^ 2 =
      (-∑ i ∈ s, a i j) % (n : ℤ) ^ 2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have hi' : (v i j : ℤ) ≡ -a i j [ZMOD (n : ℤ) ^ 2] := by
        change (v i j : ℤ) % (n : ℤ) ^ 2 = (-a i j) % (n : ℤ) ^ 2
        rw [hcanon, Int.emod_emod]
      have hs' : (∑ i ∈ s, (v i j : ℤ)) ≡ -∑ i ∈ s, a i j [ZMOD (n : ℤ) ^ 2] := ih
      simpa only [Finset.sum_insert hi, neg_add] using (hi'.add hs').eq
  have hb := integer_box_completion_subset_emod_lt n r hn a hbad s j
  rw [← he] at hb
  have hc : (((∑ i ∈ s, v i j) % n ^ 2 : ℕ) : ℤ) =
      (∑ i ∈ s, (v i j : ℤ)) % (n : ℤ) ^ 2 := by simp
  rw [← hc] at hb
  exact_mod_cast hb
