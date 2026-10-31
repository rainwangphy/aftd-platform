import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_has_ckk_subdivision

Topic: graphs   Node: c701d85fd0c0

Provenance: formalization of a published result. Source: arXiv:2610.38574 Section 1 & Section 2.1

A digraph D contains a subdivision of C(k,k) if there exist two distinct vertices u, v and two internally vertex-disjoint directed paths from u to v, each having length at least k (at least k+1 vertices).
-/

/-- A digraph D contains a subdivision of C(k,k) if it has two internally vertex-disjoint directed paths between distinct vertices, each of length at least k. -/
def digraph_has_ckk_subdivision {V : Type*} (D : Digraph V) (k : ℕ) : Prop := ∃ (u v : V) (p₁ p₂ : List V),
    u ≠ v ∧
    digraph_is_directed_path D p₁ u v ∧
    digraph_is_directed_path D p₂ u v ∧
    k + 1 ≤ p₁.length ∧
    k + 1 ≤ p₂.length ∧
    ∀ w : V, w ∈ p₁ → w ∈ p₂ → w = u ∨ w = v
