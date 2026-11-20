import AFTD.Prelude
import AFTD.Kb.Tcs.BinTree
import AFTD.Kb.Tcs.AssociahedronD
import AFTD.Kb.Tcs.AssociahedronRootLabel

/-!
# associahedron_d_stat

Topic: graphs   Node: 7a772e3021c9

Provenance: formalization of a published result. Source: arXiv:2611.19659, Section 2

The function associahedron_d_stat takes a natural number depth and a tree T : BinTree, and returns the element of ZMod 2 counting preferred left edges of T whose upper endpoint has even path depth: returning 0 for a leaf, and for a node with children l and r, if associahedron_d (associahedron_root_label l) (associahedron_root_label r) = 0 then (if depth % 2 = 0 then 1 else 0) + associahedron_d_stat (depth + 1) l + associahedron_d_stat 0 r, otherwise associahedron_d_stat 0 l + associahedron_d_stat (depth + 1) r.
-/

/-- Parity statistic d(T, depth) in ZMod 2 of preferred left edges with even path depth. -/
def associahedron_d_stat (depth : ℕ) : BinTree → ZMod 2
  | .leaf => 0
  | .node l r =>
    let a := associahedron_root_label l
    let b := associahedron_root_label r
    if associahedron_d a b = 0 then
      (if depth % 2 = 0 then (1 : ZMod 2) else 0) +
        associahedron_d_stat (depth + 1) l +
        associahedron_d_stat 0 r
    else
      associahedron_d_stat 0 l +
        associahedron_d_stat (depth + 1) r
