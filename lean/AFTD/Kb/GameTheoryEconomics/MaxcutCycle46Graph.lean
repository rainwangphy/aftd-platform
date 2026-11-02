import AFTD.Prelude

/-!
# maxcut_cycle46_graph

Topic: equilibria   Node: 7e89c784a3a8

Provenance: helper lemma. Explicit graph for the finite coalitional improvement cycle investigated under OP-85; experiment 12438.

A 46-vertex finite simple unweighted graph for a five-step strong-deviation cycle: four core blocks of eight, and two fixed-color anchor blocks of seven.
-/

def maxcut_cycle46_graph : SimpleGraph (Fin 46) := SimpleGraph.fromRel (fun (u v : Fin 46) =>
  (u.val < 8 ∧ 16 ≤ v.val ∧ v.val < 24 ∧ (v.val - 16 + 8 - u.val) % 8 < 2) ∨
  (u.val < 8 ∧ 24 ≤ v.val ∧ v.val < 32) ∨
  (u.val < 8 ∧ 39 ≤ v.val) ∨
  (8 ≤ u.val ∧ u.val < 16 ∧ 16 ≤ v.val ∧ v.val < 24 ∧
    (v.val - 16 + 8 - (u.val - 8)) % 8 < 4) ∨
  (8 ≤ u.val ∧ u.val < 16 ∧ 24 ≤ v.val ∧ v.val < 32 ∧
    2 ≤ (v.val - 24 + 8 - (u.val - 8)) % 8) ∨
  (8 ≤ u.val ∧ u.val < 16 ∧ v.val = 32) ∨
  (16 ≤ u.val ∧ u.val < 24 ∧ v.val = 39) ∨
  (24 ≤ u.val ∧ u.val < 32 ∧ 32 ≤ v.val ∧ v.val < 39))
