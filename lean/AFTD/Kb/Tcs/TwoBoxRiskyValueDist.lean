import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteDist

/-!
# two_box_risky_value_dist

Topic: online_algorithms   Node: c26252ac893c

Provenance: helper lemma. step towards two_box_counterexample_family

The distribution taking the value `M` with probability `1/M` and the value `0` with probability `1 - 1/M`.
-/

/-- The value distribution of box 1: `0` with probability `1 - 1/M`, `M` with probability `1/M`; it has mean `1`. -/
noncomputable def two_box_risky_value_dist (M : ℕ) (hM : 1 < M) : DiscreteDist where
  support := {0, (M:ℝ)}
  prob := fun v => if v = 0 then 1 - (M:ℝ)⁻¹ else (M:ℝ)⁻¹
  prob_nonneg := by
    intro v hv
    have hM1 : (1:ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt hM
    have hMpos : (0:ℝ) < M := by linarith
    split_ifs with h
    · have : (M:ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hMpos]; exact hM1
      linarith
    · positivity
  sum_prob_one := by
    have hMpos : (0:ℝ) < M := by
      have : (1:ℝ) < M := by exact_mod_cast hM
      linarith
    have hne : ((M:ℝ)) ≠ 0 := ne_of_gt hMpos
    have hne0 : (0:ℝ) ≠ (M:ℝ) := by linarith
    rw [Finset.sum_pair hne0]
    simp only [if_true, if_neg hne]
    field_simp
    ring
  val_nonneg := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · norm_num
    · positivity
