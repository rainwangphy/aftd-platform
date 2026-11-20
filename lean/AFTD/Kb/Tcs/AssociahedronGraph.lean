import AFTD.Prelude
import AFTD.Kb.Tcs.BinTree
import AFTD.Kb.Tcs.BinTreeNumLeaves
import AFTD.Kb.Tcs.TreeRotation

/-!
# associahedronGraph

Topic: graphs   Node: 4e15e702ff3c

Provenance: formalization of a published result. Source: arXiv:2611.19659, Section 2

For each natural number n, the associahedron graph associahedronGraph n is the simple graph whose vertices are ordered full binary trees T with bin_tree_num_leaves T = n - 1, and two vertices T₁ and T₂ are adjacent if and only if (TreeRotation T₁.1 T₂.1 ∨ TreeRotation T₂.1 T₁.1) and T₁ ≠ T₂.
-/

/-- The associahedron graph A_n on ordered full binary trees with n - 1 leaves. -/
def associahedronGraph (n : ℕ) : SimpleGraph { T : BinTree // bin_tree_num_leaves T = n - 1 } where
  Adj T₁ T₂ := (TreeRotation T₁.1 T₂.1 ∨ TreeRotation T₂.1 T₁.1) ∧ T₁ ≠ T₂
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩
