import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerCliqueArc
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerRootedCliqueArc

/-!
# simple_graph_cycle_power_dyadic_cover_fibre_endpoint_unique

Topic: combinatorics   Node: 32b54f05b24e

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

In any clique labeling of the cycle power C_n^{2^m-1} with n ≥ 3(2^m-1)+1, each clique contains at most one pair at distance 2^m-1.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- In any clique labeling of the cycle power C_n^{2^m-1} with n ≥ 3(2^m-1)+1, each clique contains at most one pair at distance 2^m-1. -/
theorem simple_graph_cycle_power_dyadic_cover_fibre_endpoint_unique
    (m n : ℕ) [NeZero n] (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (p q : ZMod n)
    (hp : c p = c (p + ((2 ^ m - 1 : ℕ) : ZMod n)))
    (hq : c q = c (q + ((2 ^ m - 1 : ℕ) : ZMod n)))
    (hpq : c p = c q) : p = q := by
  have harc := simple_graph_cycle_power_rooted_clique_arc n (2^m-1) hn c hc p hp
  obtain ⟨a, ha, hqa⟩ := harc q hpq.symm
  obtain ⟨b, hb, hqb⟩ := harc (q+((2^m-1 : ℕ) : ZMod n)) (hq.symm.trans hpq.symm)
  have he : ((a+(2^m-1) : ℕ) : ZMod n) = (b : ZMod n) := by
    apply add_left_cancel (a := p)
    calc
      p+((a+(2^m-1) : ℕ) : ZMod n) = (p+(a : ZMod n))+((2^m-1 : ℕ) : ZMod n) := by push_cast; ring
      _ = q+((2^m-1 : ℕ) : ZMod n) := by rw [← hqa]
      _ = p+(b : ZMod n) := hqb
  have hen : a+(2^m-1)=b := Nat.ModEq.eq_of_lt_of_lt
    ((ZMod.natCast_eq_natCast_iff _ _ n).mp he) (by omega) (by omega)
  have ha0 : a=0 := by omega
  have : q=p := by simpa only [ha0, Nat.cast_zero, add_zero] using hqa
  exact this.symm
