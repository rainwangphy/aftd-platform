import AFTD.Prelude
import AFTD.Kb.Tcs.BinTree
import AFTD.Kb.Tcs.AssociahedronQ

/-!
# associahedron_root_label

Topic: graphs   Node: efccf55273ed

Provenance: formalization of a published result. Source: arXiv:2611.19659, Section 2

The function associahedron_root_label assigns to each ordered full binary tree T a label in (ZMod 2) × (ZMod 2), defined recursively by (0, 0) for a leaf and associahedron_q (associahedron_root_label l) (associahedron_root_label r) for a node with left child l and right child r.
-/

/-- Recursive root label λ(T) in (ZMod 2) × (ZMod 2) of an ordered full binary tree. -/
def associahedron_root_label : BinTree → ZMod 2 × ZMod 2
  | .leaf => (0, 0)
  | .node l r => associahedron_q (associahedron_root_label l) (associahedron_root_label r)
