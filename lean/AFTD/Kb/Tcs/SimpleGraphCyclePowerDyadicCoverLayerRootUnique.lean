import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverFibreEndpointUnique
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverClassSpanning
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_cycle_power_dyadic_cover_layer_root_unique

Topic: combinatorics   Node: b4bde09cad7b

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

In an optimal (m+1)-layer cover of C_n^{2^m-1}, for each layer s and each vertex v, there is a unique offset a ≤ 2^m-1 such that v-a is the root spanning the class of v in layer s.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- In an optimal (m+1)-layer cover of C_n^{2^m-1}, for each layer s and each vertex v, there is a unique offset a ≤ 2^m-1 such that v-a is the root spanning the class of v in layer s. -/
theorem simple_graph_cycle_power_dyadic_cover_layer_root_unique
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin (m + 1) → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v →
      ∃ s, c s u = c s v)
    (s : Fin (m + 1)) (v : ZMod n) :
    ∃! a : ℕ, a ≤ 2 ^ m - 1 ∧
      c s (v - (a : ZMod n)) = c s v ∧
      c s (v - (a : ZMod n)) =
        c s (v - (a : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n)) := by
  obtain ⟨a, ha⟩ := simple_graph_cycle_power_dyadic_cover_class_spanning m n hm hn c hc hcov s v
  refine ⟨a, ha, ?_⟩
  intro b hb
  have he := simple_graph_cycle_power_dyadic_cover_fibre_endpoint_unique m n hn (c s) (hc s)
    (v-(b : ZMod n)) (v-(a : ZMod n)) hb.2.2 ha.2.2 (hb.2.1.trans ha.2.1.symm)
  have hecast : (b : ZMod n) = (a : ZMod n) := sub_right_inj.mp he
  exact Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ n).mp hecast) (by omega) (by omega)
