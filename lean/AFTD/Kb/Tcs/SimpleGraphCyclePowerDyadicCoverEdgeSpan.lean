import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerCliqueArc
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerRootedCliqueArc

/-!
# simple_graph_cycle_power_dyadic_cover_edge_span

Topic: combinatorics   Node: 8cbf47a05201

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

If a monochromatic clique contains v and v+d with 1 ≤ d < 2^m, its root v-a (with a ≤ 2^m-1) satisfies a < 2^m - d, so the entire edge {v, v+d} is contained in the span of v-a.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- If a monochromatic clique contains v and v+d with 1 ≤ d < 2^m, its root v-a (with a ≤ 2^m-1) satisfies a < 2^m - d, so the entire edge {v, v+d} is contained in the span of v-a. -/
theorem simple_graph_cycle_power_dyadic_cover_edge_span
    (m n : ℕ) [NeZero n] (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (v : ZMod n) (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d < 2 ^ m)
    (hcd : c v = c (v + (d : ZMod n)))
    (a : ℕ) (ha : a ≤ 2 ^ m - 1)
    (hroot : c (v - (a : ZMod n)) = c v)
    (hend : c (v - (a : ZMod n)) = c (v - (a : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n))) :
    a < 2 ^ m - d ∧ c (v - (a : ZMod n)) = c (v - (a : ZMod n) + ((a + d : ℕ) : ZMod n)) := by
  have harc := simple_graph_cycle_power_rooted_clique_arc n (2^m-1) hn c hc
    (v-(a : ZMod n)) hend
  obtain ⟨b, hb, hvb⟩ := harc (v+(d : ZMod n)) (hcd.symm.trans hroot.symm)
  have he : ((a+d : ℕ) : ZMod n) = (b : ZMod n) := by
    apply add_left_cancel (a := v-(a : ZMod n))
    calc
      (v-(a : ZMod n))+((a+d : ℕ) : ZMod n) = v+(d : ZMod n) := by push_cast; ring
      _ = (v-(a : ZMod n))+(b : ZMod n) := hvb
  have hen : a+d=b := Nat.ModEq.eq_of_lt_of_lt
    ((ZMod.natCast_eq_natCast_iff _ _ n).mp he) (by omega) (by omega)
  refine ⟨by omega, ?_⟩
  have hv : (v-(a : ZMod n))+((a+d : ℕ) : ZMod n) = v+(d : ZMod n) := by push_cast; ring
  rw [hv]
  exact hroot.trans hcd
