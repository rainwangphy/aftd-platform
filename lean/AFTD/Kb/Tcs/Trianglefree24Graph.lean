import AFTD.Prelude

/-!
# trianglefree24_graph

Topic: graphs   Node: d7849a9d90a3

Provenance: helper lemma. Explicit graph from experiments 12542 and 12544, for the triangle-free minimum-counterexample route in OP-110.

The cyclic digraph on 24 vertices with positive modular steps 1, 4, 5, 9, 13, 17 and 21.
-/

def trianglefree24_graph : Digraph (Fin 24) := ⟨fun u v => ((v.val + 24 - u.val) % 24) ∈ ({1,4,5,9,13,17,21} : Finset ℕ)⟩
