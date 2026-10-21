import AFTD.Prelude
import AFTD.Kb.Tcs.TwoBoxFairValueDist
import AFTD.Kb.Tcs.TwoBoxRiskyValueDist
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist

/-!
# two_box_deadline_inst

Topic: online_algorithms   Node: 5e198e291873

Provenance: helper lemma. step towards two_box_counterexample_family

Two boxes with zero cost: box 0 has deadline 1 and deterministic value 1; box 1 has deadline 2, value `M` with probability `1/M` and 0 otherwise.
-/

/-- Two boxes, both free to open: box 0 has deadline 1 and deterministic value 1, box 1 has deadline 2 and value `M` with probability `1/M` (0 otherwise). -/
noncomputable abbrev two_box_deadline_inst (M : ℕ) (hM : 1 < M) : PandoraDeadlineInstance where
  n := 2
  cost := fun _ => 0
  deadline := fun i => if i = 0 then 1 else 2
  dist := fun i => if i = 0 then two_box_fair_value_dist else two_box_risky_value_dist M hM
  cost_nonneg := by intro i; norm_num
  deadline_pos := by intro i; fin_cases i <;> simp
