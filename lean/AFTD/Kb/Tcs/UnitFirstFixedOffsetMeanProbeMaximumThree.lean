import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeExpectedCost
import AFTD.Kb.Tcs.LinearProbeOffset
import AFTD.Kb.Tcs.HashProbeTailCount
import AFTD.Kb.Tcs.HashProbeTailProb

/-!
# unit_first_fixed_offset_mean_probe_maximum_three

Topic: data_structures   Node: 97befe3e6ab8

Provenance: helper lemma. scout/2610-31363-a-sharp-analysis-of-fixed-offset-hash-tables.md

For a 3-slot hash table (n = 3), every bijective probe sequence r : Fin 3 → ZMod 3 with r 0 = 0 and IsUnit (r 1), and every load t < 3, the expected probe cost hash_probe_expected_cost 3 r t is at most hash_probe_expected_cost 3 (linear_probe_offset 3) t.
-/

def unit_first_fixed_offset_mean_probe_maximum_three_r_rev : Fin 3 → ZMod 3 := ![0, 2, 1]

lemma unit_first_fixed_offset_mean_probe_maximum_three_zmod3_cases (x : ZMod 3) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x
  · left; rfl
  · right; left; rfl
  · right; right; rfl

lemma unit_first_fixed_offset_mean_probe_maximum_three_fun_ext {f g : Fin 3 → ZMod 3}
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) : f = g := by
  ext ⟨i, hi⟩
  interval_cases i
  · exact h0
  · exact h1
  · exact h2

lemma unit_first_fixed_offset_mean_probe_maximum_three_r_eq_or_eq
    (r : Fin 3 → ZMod 3) (hr_inj : Function.Injective r) (hr0 : r 0 = 0) :
    r = linear_probe_offset 3 ∨ r = unit_first_fixed_offset_mean_probe_maximum_three_r_rev := by
  have h1_ne_0 : r 1 ≠ 0 := fun h => by
    have : (1 : Fin 3) = 0 := hr_inj (h.trans hr0.symm)
    revert this; decide
  have h2_ne_0 : r 2 ≠ 0 := fun h => by
    have : (2 : Fin 3) = 0 := hr_inj (h.trans hr0.symm)
    revert this; decide
  have h2_ne_1 : r 2 ≠ r 1 := fun h => by
    have : (2 : Fin 3) = 1 := hr_inj h
    revert this; decide
  rcases unit_first_fixed_offset_mean_probe_maximum_three_zmod3_cases (r 1) with hr1 | hr1 | hr1
  · exact False.elim (h1_ne_0 hr1)
  · rcases unit_first_fixed_offset_mean_probe_maximum_three_zmod3_cases (r 2) with hr2 | hr2 | hr2
    · exact False.elim (h2_ne_0 hr2)
    · rw [hr1] at h2_ne_1
      exact False.elim (h2_ne_1 hr2)
    · left
      exact unit_first_fixed_offset_mean_probe_maximum_three_fun_ext hr0 hr1 hr2
  · rcases unit_first_fixed_offset_mean_probe_maximum_three_zmod3_cases (r 2) with hr2 | hr2 | hr2
    · exact False.elim (h2_ne_0 hr2)
    · right
      exact unit_first_fixed_offset_mean_probe_maximum_three_fun_ext hr0 hr1 hr2
    · rw [hr1] at h2_ne_1
      exact False.elim (h2_ne_1 hr2)

lemma unit_first_fixed_offset_mean_probe_maximum_three_r_rev_tail_count
    (t : ℕ) (ht : t < 3) (k : ℕ) (hk : k < 4) :
    hash_probe_tail_count 3 unit_first_fixed_offset_mean_probe_maximum_three_r_rev t k =
      hash_probe_tail_count 3 (linear_probe_offset 3) t k := by
  interval_cases t <;> interval_cases k <;> decide

lemma unit_first_fixed_offset_mean_probe_maximum_three_r_rev_expected_cost
    (t : ℕ) (ht : t < 3) :
    hash_probe_expected_cost 3 unit_first_fixed_offset_mean_probe_maximum_three_r_rev t =
      hash_probe_expected_cost 3 (linear_probe_offset 3) t := by
  unfold hash_probe_expected_cost hash_probe_tail_prob
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [unit_first_fixed_offset_mean_probe_maximum_three_r_rev_tail_count t ht k hk]

/-- OP-805 holds for all loads t < 3 on a table of size 3. -/
theorem unit_first_fixed_offset_mean_probe_maximum_three
    (r : Fin 3 → ZMod 3) (hr_bij : Function.Bijective r)
    (hr0 : r 0 = 0) (hr1 : IsUnit (r 1))
    (t : ℕ) (ht : t < 3) :
    hash_probe_expected_cost 3 r t ≤ hash_probe_expected_cost 3 (linear_probe_offset 3) t := by
  rcases unit_first_fixed_offset_mean_probe_maximum_three_r_eq_or_eq r hr_bij.injective hr0 with rfl | rfl
  · exact le_rfl
  · rw [unit_first_fixed_offset_mean_probe_maximum_three_r_rev_expected_cost t ht]
