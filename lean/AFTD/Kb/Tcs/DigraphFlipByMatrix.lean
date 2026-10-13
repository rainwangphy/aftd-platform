import AFTD.Prelude

/-!
# digraph_flip_by_matrix

Topic: graphs   Node: a7d9df41092f

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 2.2 (decycling matrix: flipping all arcs uv with M_uv = 1).

Given a digraph D and a (symmetric) matrix M over F₂ indexed by its vertices, the digraph obtained by reversing every arc uv with M_uv = 1 and keeping the others.
-/

/-- Reverse every arc `u v` of `D` with `M u v = 1`, keep the others. -/
def digraph_flip_by_matrix {V : Type*} (D : Digraph V) (M : Matrix V V (ZMod 2)) : Digraph V where
  Adj x y := (M x y = 1 ∧ D.Adj y x) ∨ (M x y ≠ 1 ∧ D.Adj x y)
