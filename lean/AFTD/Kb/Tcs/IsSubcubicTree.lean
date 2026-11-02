import AFTD.Prelude

/-!
# is_subcubic_tree

Topic: approximation   Node: 1a528257094e

Provenance: formalization of a published result. Source: arXiv:2610.39863, Section 3

A finite simple graph is a subcubic tree if it is connected, acyclic, and every vertex has degree at most 3.
-/

/-- A finite simple graph is a subcubic tree (an unrooted binary tree) if it is a tree and every vertex has degree at most 3. -/
def is_subcubic_tree {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop := G.IsTree ∧ open Classical in ∀ v : α, G.degree v ≤ 3
