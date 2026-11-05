import AFTD.Prelude

/-!
# zmod19_edge_color

Topic: combinatorics   Node: 747ee08ff656

Provenance: formalization of a published result. Source: arXiv:2611.03878 Theorem 3.2

The 3-edge-coloring of the complete graph on vertices ZMod 19 assigns color 0 to an edge {x, y} if y - x is in the cubic residue set H = {1, 7, 8, 11, 12, 18}, color 1 if y - x is in 2H, and color 2 otherwise (in 4H).
-/

/-- The three-edge-coloring of the complete graph on ZMod 19 based on cubic residue cosets modulo 19. -/
def zmod19_edge_color (x y : ZMod 19) : Fin 3 :=
  if y - x ∈ ({1, 7, 8, 11, 12, 18} : Finset (ZMod 19)) then 0
  else if y - x ∈ ({1, 7, 8, 11, 12, 18} : Finset (ZMod 19)).image (2 * ·) then 1
  else 2
