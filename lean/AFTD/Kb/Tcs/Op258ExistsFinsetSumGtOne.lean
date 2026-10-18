import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_258_exists_finset_sum_gt_one

Topic: combinatorics   Node: 1fa9056c1adc

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

If f : α → ℝ is nonnegative and its ENNReal-sum of ENNReal.ofReal (f ·) is strictly greater than 1, then some finite set I of indices and some δ > 0 satisfy 1 + δ ≤ Σ_{i∈I} f i.
-/

/-- A sum strictly greater than 1 is already exceeded by a finite partial sum: some finite set of colours carries mass `1 + δ` with `δ > 0`. -/
theorem op_258_exists_finset_sum_gt_one {α : Type*} (f : α → ℝ) (h0 : ∀ i, 0 ≤ f i)
    (hsum : 1 < ∑' i : α, ENNReal.ofReal (f i)) :
    ∃ (I : Finset α) (δ : ℝ), 0 < δ ∧ 1 + δ ≤ ∑ i ∈ I, f i := by
  rw [ENNReal.tsum_eq_iSup_sum] at hsum
  obtain ⟨I, hI⟩ := lt_iSup_iff.mp hsum
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i)] at hI
  have hpos : 0 < ∑ i ∈ I, f i :=
    ENNReal.ofReal_pos.mp (lt_of_lt_of_le (show (0 : ENNReal) < 1 from zero_lt_one) hI.le)
  rw [← ENNReal.ofReal_one] at hI
  have hgt : 1 < ∑ i ∈ I, f i := (ENNReal.ofReal_lt_ofReal_iff hpos).mp hI
  exact ⟨I, (∑ i ∈ I, f i) - 1, by linarith, by linarith⟩
