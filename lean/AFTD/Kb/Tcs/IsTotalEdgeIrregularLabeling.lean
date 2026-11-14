import AFTD.Prelude

/-!
# is_total_edge_irregular_labeling

Topic: graphs   Node: 010c6dcc3456

Provenance: formalization of a published result. Source: arXiv:2611.16338, Section 1

A vertex labeling φ : V → ℕ and an edge labeling ψ : G.edgeSet → ℕ form a total edge irregular s-labeling of a simple graph G if all vertex labels and edge labels are between 1 and s inclusive, and the total edge weights φ(u) + ψ(uv) + φ(v) are pairwise distinct for all edges uv of G.
-/

/-- A total edge irregular s-labeling of a simple graph G. -/
def is_total_edge_irregular_labeling {V : Type*} (G : SimpleGraph V) (s : ℕ)
    (φ : V → ℕ) (ψ : G.edgeSet → ℕ) : Prop :=
  (∀ v : V, 1 ≤ φ v ∧ φ v ≤ s) ∧
  (∀ e : G.edgeSet, 1 ≤ ψ e ∧ ψ e ≤ s) ∧
  ∀ (e₁ e₂ : G.edgeSet),
    Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e₁.val + ψ e₁ =
    Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e₂.val + ψ e₂ → e₁ = e₂
