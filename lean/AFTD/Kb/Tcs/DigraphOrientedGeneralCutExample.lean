import AFTD.Prelude

/-!
# digraph_oriented_general_cut_example

Topic: graphs   Node: 2cbaf7d52af9

Provenance: helper lemma. Parametric extension of experiment 26321, checked for d=3,...,7 in experiment 26332.

A parametric oriented cut example with d−2 transitive low vertices, a target, a directed d-cycle, d acyclic high vertices and d−1 sinks.
-/

def digraph_oriented_general_cut_example (d : ℕ) : Digraph (Fin (4 * d - 2)) := ⟨fun u v =>
  (u.val < d - 2 ∧ (v.val < u.val ∨ v.val = d - 2 ∨
    (3 * d - 1 ≤ v.val ∧ u.val + v.val < 4 * d - 2))) ∨
  (u.val = d - 2 ∧ 2 * d - 1 ≤ v.val ∧ v.val < 3 * d - 1) ∨
  (d - 1 ≤ u.val ∧ u.val < 2 * d - 1 ∧
    (v.val < d - 1 ∨ v.val = d - 1 + (u.val - (d - 1) + 1) % d)) ∨
  (2 * d - 1 ≤ u.val ∧ u.val < 3 * d - 1 ∧
    ((2 * d - 1 ≤ v.val ∧ v.val < u.val) ∨
      (d - 1 ≤ v.val ∧ u.val + v.val < 4 * d - 2)))⟩
