import AFTD.Prelude

/-!
# simple_graph_size_ramsey_arrows

Topic: graphs   Node: 1fc52eaffb17

Provenance: formalization of a published result. Source: arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Section 1: definition of G → (F, H)

G → (F, H): every red/blue colouring of the edges of G has a red copy of F or a blue copy of H. The red edges form a subgraph R ≤ G and the blue edges are G \ R; a copy is a subgraph isomorphic to the graph.
-/

def simple_graph_size_ramsey_arrows {V α β : Type*} (G : SimpleGraph V) (F : SimpleGraph α)
    (H : SimpleGraph β) : Prop :=
  ∀ R : SimpleGraph V, R ≤ G → F.IsContained R ∨ H.IsContained (G \ R)
