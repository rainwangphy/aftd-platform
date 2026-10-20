import AFTD.Prelude

/-!
# simple_graph_is_cactus

Topic: automata   Node: 78c9ec241172

Provenance: formalization of a published result. Source: arXiv:2610.11717 Sec. 2

A simple graph is a cactus if any two simple cycles that share an edge have identical edge sets (every edge belongs to at most one simple cycle).
-/

/-- A simple graph is a cactus if every edge belongs to at most one simple cycle. -/
def simple_graph_is_cactus {V : Type*} (G : SimpleGraph V) : Prop := ∀ ⦃u₁ u₂ : V⦄ (p₁ : G.Walk u₁ u₁) (p₂ : G.Walk u₂ u₂),
    p₁.IsCycle → p₂.IsCycle →
    (∃ e, e ∈ p₁.edges ∧ e ∈ p₂.edges) →
    p₁.toSubgraph = p₂.toSubgraph
