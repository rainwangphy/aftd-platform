import AFTD.Prelude

/-!
# digraph_digon_minimum_inweight_half_cover_counterexample

Topic: graphs   Node: 9fbaa268546c

Provenance: helper lemma. Explicit finite counterexample to extending the oriented-graph minimum-inweight construction directly to digons, experiment 14481. Other quasi-kernels may still half-cover the weights.

The displayed loopless semicomplete four-vertex digraph has vertex 0 minimizing both weighted in-degree and in-degree; its singleton is a quasi-kernel but covers less than half the displayed total weight in its closed out-neighborhood.
-/

open scoped BigOperators

def in541_digon_out (v : Fin 4) : Finset (Fin 4) :=
  if v = 0 then {3} else if v = 1 then {0,2,3} else
  if v = 2 then {0,1,3} else {1,2}

def in541_digon_weight (v : Fin 4) : ℕ :=
  if v = 0 then 1 else if v = 1 then 4 else if v = 2 then 3 else 4

theorem digraph_digon_minimum_inweight_half_cover_counterexample :
    (∀ v, v ∉ in541_digon_out v) ∧
    (∀ u v, u ≠ v → v ∈ in541_digon_out u ∨ u ∈ in541_digon_out v) ∧
    (∀ v : Fin 4,
      (∑ u ∈ Finset.univ.filter (fun u => (0 : Fin 4) ∈ in541_digon_out u), in541_digon_weight u) ≤
      (∑ u ∈ Finset.univ.filter (fun u => v ∈ in541_digon_out u), in541_digon_weight u)) ∧
    (∀ v : Fin 4,
      (Finset.univ.filter (fun u => (0 : Fin 4) ∈ in541_digon_out u)).card ≤
      (Finset.univ.filter (fun u => v ∈ in541_digon_out u)).card) ∧
    (∀ v, v = 0 ∨ v ∈ in541_digon_out 0 ∨
      ∃ z, z ∈ in541_digon_out 0 ∧ v ∈ in541_digon_out z) ∧
    2 * (∑ v ∈ Finset.univ.filter (fun v => v = 0 ∨ v ∈ in541_digon_out 0),
      in541_digon_weight v) < ∑ v, in541_digon_weight v := by
  decide
