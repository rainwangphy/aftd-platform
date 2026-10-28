import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerCliqueArc
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverTightLongEdges
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelVertexLayers
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelExactDyadic
import AFTD.Kb.Tcs.CyclePowerDyadicPeriodicModelTightOfCounts

/-!
# simple_graph_cycle_power_dyadic_class_model_tight_weights

Topic: combinatorics   Node: dbf74ec4b0a6

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

Every rooted dyadic class of an optimal cover is tight: the dyadic class weight of the arc equals its cardinality.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Tight class weights: the dyadic class weight of an active arc equals its cardinality. -/
theorem simple_graph_cycle_power_dyadic_class_model_tight_weights
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin (m + 1) → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v →
      ∃ s, c s u = c s v)
    (ell : ℤ → Fin (m + 1))
    (hellroot : ∀ p : ℤ,
      c (ell p) ((p : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n)) = c (ell p) (p : ZMod n))
    (p : ℤ) :
    cycle_power_dyadic_class_weight m
        (fun a => decide (a < 2 ^ m ∧
          c (ell p) ((p : ZMod n) + (a : ZMod n)) = c (ell p) (p : ZMod n)))
      = (Finset.range (2 ^ m)).sum (fun a =>
          (decide (a < 2 ^ m ∧
            c (ell p) ((p : ZMod n) + (a : ZMod n)) = c (ell p) (p : ZMod n))).toNat) := by
  classical
  have ht := (simple_graph_cycle_power_dyadic_cover_tight_long_edges m n hm hn c hc hcov).1
  have huniq (q : ℤ) (s : Fin (m+1))
      (hs : c s ((q : ZMod n)+((2^m-1 : ℕ) : ZMod n)) = c s (q : ZMod n)) : s=ell q :=
    (ht (q : ZMod n)).unique hs.symm (hellroot q).symm
  have hper (q : ℤ) : ell (q+(n : ℤ)) = ell q := by
    apply huniq q
    simpa only [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero] using hellroot (q+(n : ℤ))
  let x : ℤ → ℕ → Bool := fun q a => decide (a < 2^m ∧
    c (ell q) ((q : ZMod n)+(a : ZMod n)) = c (ell q) (q : ZMod n))
  have hxp (q : ℤ) (a : ℕ) : x (q+(n : ℤ)) a = x q a := by
    simp only [x, hper, Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]
  have hxc := simple_graph_cycle_power_dyadic_class_model_vertex_layers m n hm hn c hc hcov ell hellroot huniq
  have hxe := simple_graph_cycle_power_dyadic_class_model_exact_dyadic m n hm hn c hc hcov ell hellroot huniq
  exact cycle_power_dyadic_periodic_model_tight_of_counts m n hm x hxp hxc hxe p
