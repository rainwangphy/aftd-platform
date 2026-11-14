import AFTD.Prelude

/-!
# digraph_oriented_cut20_sharp_example

Topic: graphs   Node: 9b82bb5262d4

Provenance: helper lemma. Explicit construction from experiment 26321.

The explicit oriented 26-vertex graph with five low vertices, a target, a directed seven-cycle, seven acyclic high vertices and six sinks.
-/

def digraph_oriented_cut20_sharp_example : Digraph (Fin 26) := ⟨fun u v =>
  (u.val < 5 ∧ (v.val < u.val ∨ v.val = 5 ∨ (20 ≤ v.val ∧ u.val + v.val < 26))) ∨
  (u.val = 5 ∧ 13 ≤ v.val ∧ v.val < 20) ∨
  (6 ≤ u.val ∧ u.val < 13 ∧ (v.val < 6 ∨ v.val = 6 + (u.val - 6 + 1) % 7)) ∨
  (13 ≤ u.val ∧ u.val < 20 ∧ ((13 ≤ v.val ∧ v.val < u.val) ∨ (6 ≤ v.val ∧ u.val + v.val < 26)))⟩
