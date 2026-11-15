import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactBlock
import AFTD.Kb.Tcs.Op75CompactBlockEffect
import AFTD.Kb.Tcs.Op75Run
import AFTD.Kb.Tcs.Op75CompactMap
import AFTD.Kb.Tcs.Op75CompactDigit
import AFTD.Kb.Tcs.EvalHiddenLayer
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# op75_fold_blocks

Topic: np_completeness   Node: aa60cdfadcaa

Provenance: helper lemma. OP-75, arXiv:2610.06092: proof of the explicit single-pass subset-sum network.

For a nonnegative initial accumulator and an initial point in the unit interval, folding the seven-layer blocks gives the final orbit coordinate, the initial accumulator plus the orbit sum, and zero in the third coordinate.
-/

theorem op75_fold_blocks (as : List ℕ) (x p : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hp : 0 ≤ p) :
    ((as.flatMap op75_compact_block).foldl (fun v l => evalHiddenLayer l v) ![x,p,0]) =
      ![(op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).1,
        p + (op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).2, 0] := by
  induction as generalizing x p with
  | nil => simp [op75_run]
  | cons a as ih =>
      simp only [List.flatMap_cons, List.foldl_append]
      rw [op75_compact_block_effect x p a hx hp]
      have hF : op75_compact_map x ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · unfold op75_compact_map
          exact le_min (by norm_num) (le_min (by linarith [hx.1]) (abs_nonneg _))
        · exact min_le_left _ _
      have hE : 0 ≤ op75_compact_digit x := le_max_left _ _
      have hp' : 0 ≤ p + (a:ℝ)*op75_compact_digit x := by positivity
      rw [ih (op75_compact_map x) (p + (a:ℝ)*op75_compact_digit x) hF hp']
      simp only [List.map_cons, op75_run, add_assoc]
