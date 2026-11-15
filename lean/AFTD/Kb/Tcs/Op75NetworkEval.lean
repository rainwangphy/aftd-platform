import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactNetwork
import AFTD.Kb.Tcs.Op75CompactFinal
import AFTD.Kb.Tcs.Op75CompactLayer
import AFTD.Kb.Tcs.Op75FoldBlocks
import AFTD.Kb.Tcs.Op75RunInvariants
import AFTD.Kb.Tcs.Op75Run
import AFTD.Kb.Tcs.Op75CompactMap
import AFTD.Kb.Tcs.Op75CompactDigit
import AFTD.Kb.Tcs.EvalNetwork
import AFTD.Kb.Tcs.EvalHiddenLayer
import AFTD.Kb.Tcs.ReLUHiddenLayer
import AFTD.Kb.Tcs.Op75CompactBlock

/-!
# op75_network_eval

Topic: np_completeness   Node: 2346651761f3

Provenance: helper lemma. OP-75, arXiv:2610.06092: proof of the explicit single-pass subset-sum network.

For a unit-interval input, the explicit subset-sum network evaluates to the final orbit coordinate plus the absolute difference between its accumulated sum and the target.
-/

theorem op75_network_eval (as : List ℕ) (t : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    evalNetwork (op75_compact_network as t) x =
      (op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).1 +
        |(op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).2 - (t:ℝ)| := by
  let q := op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x
  have hq : q.1 ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ q.2 := op75_run_invariants as x hx
  have hfold := op75_fold_blocks as x 0 hx (by norm_num)
  change ((as.flatMap op75_compact_block).foldl (fun v l => evalHiddenLayer l v) ![x,0,0]) = ![q.1, 0+q.2, 0] at hfold
  have hinit : (fun i : Fin 3 => (((![1,0,0] : Fin 3 → ℚ) i : ℝ) * x + (((![0,0,0] : Fin 3 → ℚ) i : ℝ)))) = ![x,0,0] := by
    funext i
    fin_cases i <;> simp
  simp only [evalNetwork, op75_compact_network]
  rw [hinit, List.foldl_append, hfold]
  simp only [List.foldl_cons, List.foldl_nil, zero_add, Rat.cast_zero]
  change (∑ i, ((![1,1,1] : Fin 3 → ℚ) i : ℝ) *
    (evalHiddenLayer (op75_compact_final t) ![q.1,q.2,0]) i) + 0 = q.1 + |q.2 - (t:ℝ)|
  by_cases h : q.2 ≤ (t:ℝ)
  · have ha : q.2 - (t:ℝ) ≤ 0 := by linarith
    have hb : 0 ≤ (t:ℝ) - q.2 := by linarith
    rw [abs_of_nonpos ha]
    simp [evalHiddenLayer,op75_compact_final,op75_compact_layer,relu,Fin.sum_univ_three,
      max_eq_left hq.1.1]
    have ha' : q.2 + -(t:ℝ) ≤ 0 := by linarith
    rw [max_eq_right ha']
    have hb' : 0 ≤ -q.2 + (t:ℝ) := by linarith
    rw [max_eq_left hb']
    ring
  · have ha : 0 ≤ q.2 - (t:ℝ) := by linarith
    have hb : (t:ℝ) - q.2 ≤ 0 := by linarith
    rw [abs_of_nonneg ha]
    simp [evalHiddenLayer,op75_compact_final,op75_compact_layer,relu,Fin.sum_univ_three,
      max_eq_left hq.1.1]
    have ha' : 0 ≤ q.2 + -(t:ℝ) := by linarith
    rw [max_eq_left ha']
    have hb' : -q.2 + (t:ℝ) ≤ 0 := by linarith
    rw [max_eq_right hb']
    ring
