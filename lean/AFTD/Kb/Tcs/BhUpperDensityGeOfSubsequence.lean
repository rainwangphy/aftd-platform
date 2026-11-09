import AFTD.Prelude
import AFTD.Kb.Tcs.BhCounting
import AFTD.Kb.Tcs.BhUpperDensity

/-!
# bh_upper_density_ge_of_subsequence

Topic: combinatorics   Node: 94ad9126d097

Provenance: helper lemma. step towards op_939_optimal_upper_density_strictly_greater

If a set A has normalized counting function at least c along a strictly increasing sequence of checkpoints, and the normalized counting function is bounded from above, then its normalized upper density is at least c.
-/

/-- If a set A has normalized counting function at least c along a strictly increasing sequence of checkpoints, and the normalized counting function is bounded under le, then its normalized upper density is at least c. -/
theorem bh_upper_density_ge_of_subsequence (h : ℕ) (A : Set ℕ) (x : ℕ → ℕ)
    (hx : ∀ k, x k < x (k + 1)) (c : ℝ)
    (h_bd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n : ℕ => ((bh_counting A n : ℝ)) / ((n : ℝ) ^ ((1 : ℝ) / (h : ℝ)))))
    (hc : ∀ k, c ≤ ((bh_counting A (x k) : ℝ)) / ((x k : ℝ) ^ ((1 : ℝ) / (h : ℝ)))) :
    c ≤ bh_upper_density h A := by
  have hmono : StrictMono x := strictMono_nat_of_lt_succ hx
  have hfreq : ∃ᶠ n in Filter.atTop, c ≤ ((bh_counting A n : ℝ)) / ((n : ℝ) ^ ((1 : ℝ) / (h : ℝ))) := by
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (Filter.Tendsto.eventually_ge_atTop hmono.tendsto_atTop a)
    exact ⟨x K, hK K le_rfl, hc K⟩
  exact Filter.le_limsup_of_frequently_le hfreq h_bd
