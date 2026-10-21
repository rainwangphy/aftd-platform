import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteDist

/-!
# two_box_fair_value_dist

Topic: online_algorithms   Node: ad2bd40c97df

Provenance: helper lemma. step towards two_box_counterexample_family

The degenerate discrete distribution taking the value `1` with probability `1`.
-/

/-- The point mass at `1`, used as the value distribution of box 0. -/
noncomputable def two_box_fair_value_dist : DiscreteDist := { support := {1}, prob := fun _ => 1, prob_nonneg := by intro v hv; norm_num, sum_prob_one := by simp, val_nonneg := by intro v hv; simp at hv; linarith }
