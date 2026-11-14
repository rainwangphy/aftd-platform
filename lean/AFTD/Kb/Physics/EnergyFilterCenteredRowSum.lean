import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# energy_filter_centered_row_sum

Topic: statistical_mechanics   Node: 4fbba0de8398

Provenance: helper lemma. OP-892: binomial-row specialization of the exact trace reindexing.

For any real integer function, summing it over offsets from −k to k equals summing it at j−k over j from 0 through 2k.
-/

theorem energy_filter_centered_row_sum (k : ℕ) (f : ℤ → ℝ) :
    (∑ t ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), f t) =
      ∑ j ∈ Finset.range (2*k+1), f ((j:ℤ)-(k:ℤ)) := by
  apply Finset.sum_bij (fun t _ => ((k:ℤ)+t).toNat)
  · intro t ht
    rw [Finset.mem_Icc] at ht
    rw [Finset.mem_range]
    omega
  · intro a ha b hb hab
    rw [Finset.mem_Icc] at ha hb
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    refine ⟨(j:ℤ)-(k:ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · omega
  · intro t ht
    rw [Finset.mem_Icc] at ht
    have he : ((((k:ℤ)+t).toNat:ℤ)-(k:ℤ)) = t := by omega
    rw [he]
