import AFTD.Prelude
import AFTD.Kb.Tcs.BinTree
import AFTD.Kb.Tcs.AssociahedronRootLabel
import AFTD.Kb.Tcs.AssociahedronDStat

/-!
# associahedron_colouring

Topic: graphs   Node: 0435156abdae

Provenance: formalization of a published result. Source: arXiv:2611.19659, Section 2

The function associahedron_colouring assigns to each ordered full binary tree T the pair (associahedron_root_label T, associahedron_d_stat 0 T) in ((ZMod 2) × (ZMod 2)) × ZMod 2.
-/

/-- The 8-colouring κ(T) = (λ(T), d(T, 0)) in ((ZMod 2) × (ZMod 2)) × ZMod 2. -/
def associahedron_colouring (T : BinTree) : (ZMod 2 × ZMod 2) × ZMod 2 := (associahedron_root_label T, associahedron_d_stat 0 T)
