import AFTD.Prelude

/-!
# digraph_cut20_sharp_example

Topic: graphs   Node: 5d8976fb29b5

Provenance: helper lemma. Extension of the two-cycle extremal construction in https://arxiv.org/abs/2205.10826, Figure 3.2; experiment 26197.

An explicit 20-vertex digraph obtained by adjoining seven sink vertices to the displayed 13-vertex two-cycle obstruction.
-/

def digraph_cut20_sharp_example : Digraph (Fin 20) := ⟨fun u v =>
  (u.val < 7 ∧ (v.val = (u.val + 1) % 7 ∨ v.val = 7 ∨ (8 ≤ v.val ∧ v.val < 13))) ∨
  (u.val = 7 ∧ v.val < 7) ∨
  (8 ≤ u.val ∧ u.val < 13 ∧
    (v.val = 7 ∨ (8 ≤ v.val ∧ v.val < u.val) ∨ (13 ≤ v.val ∧ u.val + v.val < 27)))⟩
