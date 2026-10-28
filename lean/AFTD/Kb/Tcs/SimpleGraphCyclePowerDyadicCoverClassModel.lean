import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.SimpleGraphCyclePowerAdjIffOfBandwidthLt
import AFTD.Kb.Tcs.SimpleGraphCyclePowerCliqueArc
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverTightLongEdges
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverClassSpanning
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicLayerWeightLe
import AFTD.Kb.Tcs.CyclePowerDyadicIntWeightLeCard
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverFibreEndpointUnique
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverLayerRootUnique
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverEdgeSpan
import AFTD.Kb.Tcs.ZmodSumSubEqSum
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightEqOfSumEq
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelDisjointColours
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelVertexLayers
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelExactDyadic
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelOrdinaryCover
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelTightWeights
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelLayerChoice

/-!
# simple_graph_cycle_power_dyadic_cover_class_model

Topic: combinatorics   Node: 5659c27fcd2a

Provenance: helper lemma. Uniform actual-cover to class-model bridge for OP-205 / RT-1, following arXiv:2610.15635. This packages the proved geometric and weight-saturation lemmas; it does not prove rigidity, pruning counts or the main conjecture. No research advance claimed.

Every optimal dyadic cycle-power equivalence cover admits a faithful periodic integer class model with the original rooted classes and real layer colours, tight class weights, constant active counts, exact dyadic coverage, all ordinary coverage, and disjoint active classes of the same colour.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_cycle_power_dyadic_cover_class_model
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin (m + 1) → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v →
      ∃ s, c s u = c s v) :
    ∃ (x : ℤ → ℕ → Bool) (ell : ℤ → Fin (m + 1)),
      (∀ p a, x (p + (n : ℤ)) a = x p a) ∧
      (∀ p, ell (p + (n : ℤ)) = ell p) ∧
      (∀ p, x p 0 = true ∧ x p (2 ^ m - 1) = true) ∧
      (∀ p, cycle_power_dyadic_class_weight m (x p) =
        (Finset.range (2 ^ m)).sum (fun a => (x p a).toNat)) ∧
      (∀ v : ℤ, (Finset.range (2 ^ m)).sum
        (fun a => (x (v - (a : ℤ)) a).toNat) = m + 1) ∧
      (∀ j < m, ∀ v : ℤ, (Finset.range (2 ^ j)).sum (fun a =>
        (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j)).toNat) = 1) ∧
      (∀ d : ℕ, 1 ≤ d → d < 2 ^ m → ∀ v : ℤ,
        ∃ a : ℕ, a < 2 ^ m - d ∧ x (v - (a : ℤ)) a = true ∧
          x (v - (a : ℤ)) (a + d) = true) ∧
      (∀ p a, x p a = true →
        c (ell p) ((p : ZMod n) + (a : ZMod n)) = c (ell p) (p : ZMod n)) ∧
      (∀ (v : ℤ) (a b : ℕ), a < 2 ^ m → b < 2 ^ m → a ≠ b →
        x (v - (a : ℤ)) a = true → x (v - (b : ℤ)) b = true →
        ell (v - (a : ℤ)) ≠ ell (v - (b : ℤ))) := by
  classical
  obtain ⟨ell, hper, hroot, huniq⟩ := simple_graph_cycle_power_dyadic_class_model_layer_choice m n hm hn c hc hcov
  let x : ℤ → ℕ → Bool := fun p a => decide (a < 2^m ∧
    c (ell p) ((p : ZMod n)+(a : ZMod n)) = c (ell p) (p : ZMod n))
  have hxp (p : ℤ) (a : ℕ) : x (p+(n : ℤ)) a = x p a := by
    simp only [x, hper, Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]
  have hends (p : ℤ) : x p 0 = true ∧ x p (2^m-1) = true := by
    constructor
    · simp [x, Nat.two_pow_pos]
    · apply decide_eq_true
      exact ⟨by have := Nat.two_pow_pos m; omega, hroot p⟩
  have htw := simple_graph_cycle_power_dyadic_class_model_tight_weights m n hm hn c hc hcov ell hroot
  have hct := simple_graph_cycle_power_dyadic_class_model_vertex_layers m n hm hn c hc hcov ell hroot huniq
  have hex := simple_graph_cycle_power_dyadic_class_model_exact_dyadic m n hm hn c hc hcov ell hroot huniq
  have hcv := simple_graph_cycle_power_dyadic_class_model_ordinary_cover m n hm hn c hc hcov ell hroot huniq
  refine ⟨x, ell, hxp, hper, hends, htw, hct, hex, hcv, ?_, ?_⟩
  · intro p a ha
    exact (of_decide_eq_true ha).2
  · intro v a b ha hb hab hxa hxb
    exact simple_graph_cycle_power_dyadic_class_model_disjoint_colours m n hm hn c hc hcov ell hroot huniq
      v a b ha hb hab (of_decide_eq_true hxa).2 (of_decide_eq_true hxb).2
