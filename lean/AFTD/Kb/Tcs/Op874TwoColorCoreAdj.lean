import AFTD.Prelude

/-!
# op874_two_color_core_adj

Topic: graphs   Node: 5abbbbd078ad

Provenance: helper lemma. Local-state counting obstruction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

The nine undirected edges of a two-color missing-palette obstruction.
-/

def op874_two_color_core_adj (v w : Fin 10) : Prop :=
  (v,w) ∈ ({(0,6),(6,0),(0,9),(9,0),(6,9),(9,6),(7,9),(9,7),
            (2,4),(4,2),(2,8),(8,2),(4,8),(8,4),(5,8),(8,5),
            (4,6),(6,4)} : Finset (Fin 10 × Fin 10))
