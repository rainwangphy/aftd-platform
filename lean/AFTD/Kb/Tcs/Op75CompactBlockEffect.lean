import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactBlock
import AFTD.Kb.Tcs.Op75CompactMap
import AFTD.Kb.Tcs.Op75CompactDigit
import AFTD.Kb.Tcs.Op75CompactMapRelu
import AFTD.Kb.Tcs.Op75CompactDigitRelu
import AFTD.Kb.Tcs.EvalHiddenLayer
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# op75_compact_block_effect

Topic: np_completeness   Node: 1e64091858f5

Provenance: helper lemma. OP-75, arXiv:2610.06092; explicit seven-layer single-pass subset-sum construction.

For an input in the unit interval and a nonnegative accumulator, the seven-layer block for a nonnegative integer weight transforms the state (x,p,0) to (F(x),p+a E(x),0), using the compact map F and digit selector E.
-/

theorem op75_compact_block_effect (x p : ℝ) (a : ℕ) (hx : x ∈ Set.Icc 0 1) (hp : 0 ≤ p) : (op75_compact_block a).foldl (fun v layer => evalHiddenLayer layer v) ![x,p,0] = ![op75_compact_map x, p + (a : ℝ) * op75_compact_digit x, 0] := by
  have hE : 0 ≤ op75_compact_digit x := le_max_left _ _
  have hA : (0:ℝ) ≤ a := Nat.cast_nonneg _
  have hpre : 0 ≤ p + (a:ℝ) * max (4*x-1) 0 := by positivity
  have hpost : 0 ≤ p + (a:ℝ) * max (4*x-1) 0 - (a:ℝ)*max (4*x-2) 0 := by
    have hh := mul_nonneg hA hE
    rw [op75_compact_digit_relu] at hh
    nlinarith
  have hF : 0 ≤ op75_compact_map x := by
    unfold op75_compact_map
    exact le_min (by norm_num) (le_min (by linarith [hx.1]) (abs_nonneg _))
  have hpos : 0 ≤ 1 - max (1-4*x + max (8*x-3 - max (8*x-6) 0) 0) 0 := by
    rw [← op75_compact_map_relu x hx]
    exact hF
  funext i
  fin_cases i <;>
    simp [op75_compact_block, op75_compact_layer, evalHiddenLayer, relu,
      Fin.sum_univ_three, max_eq_left hx.1, max_eq_left hp, max_eq_left hpre,
      max_eq_left hpost, max_eq_left hpos, op75_compact_digit_relu,
      op75_compact_map_relu x hx]
  all_goals ring_nf at hpos hpre hpost ⊢
  · exact max_eq_left hpos
  · rw [max_eq_left hpre]
    have hpost' : 0 ≤ -((a:ℝ)*max (-2+x*4) 0) + (p+(a:ℝ)*max (-1+x*4) 0) := by linarith
    rw [max_eq_left hpost']
    ring
