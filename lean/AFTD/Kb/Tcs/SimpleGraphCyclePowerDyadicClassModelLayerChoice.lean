import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverTightLongEdges
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_cycle_power_dyadic_class_model_layer_choice

Topic: combinatorics   Node: 55f1d6dd0a0c

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

There is a periodic integer layer map ell assigning to each integer p the unique layer covering the endpoint pair (p, p+2^m-1), with uniqueness among all layers.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Canonical layer assignment: the unique covering layer of each endpoint-distance pair, extended periodically to the integers. -/
theorem simple_graph_cycle_power_dyadic_class_model_layer_choice
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin (m + 1) → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v →
      ∃ s, c s u = c s v) :
    ∃ ell : ℤ → Fin (m + 1),
      (∀ p : ℤ, ell (p + (n : ℤ)) = ell p) ∧
      (∀ p : ℤ,
        c (ell p) ((p : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n)) = c (ell p) (p : ZMod n)) ∧
      (∀ (p : ℤ) (s : Fin (m + 1)),
        c s ((p : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n)) = c s (p : ZMod n) → s = ell p) := by
  classical
  have ht := (simple_graph_cycle_power_dyadic_cover_tight_long_edges m n hm hn c hc hcov).1
  let f : ZMod n → Fin (m+1) := fun p => (ht p).choose
  have hf (p : ZMod n) := (ht p).choose_spec
  refine ⟨fun p => f (p : ZMod n), ?_, ?_, ?_⟩
  · intro p
    simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]
  · intro p
    exact (hf (p : ZMod n)).1.symm
  · intro p s hs
    exact (hf (p : ZMod n)).2 s hs.symm
