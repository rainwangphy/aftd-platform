import AFTD.Prelude

/-!
# op874_odd_transversal_cycle_index

Topic: graphs   Node: 80a1dfde3b90

Provenance: helper lemma. Explicit one-sided nonadjacent-defect obstruction adapted from https://arxiv.org/html/2309.12150 section 2.2, experiment 35359.

The cycle component index of each vertex in the displayed two-factor.
-/

def op874_odd_transversal_cycle_index (v : Fin 42) : Fin 10 := if v.val < 21 then Fin.ofNat 10 (v.val / 7) else Fin.ofNat 10 (3 + (v.val - 21) / 3)
