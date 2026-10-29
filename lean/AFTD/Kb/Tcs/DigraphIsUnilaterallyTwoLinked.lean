import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_is_unilaterally_two_linked

Topic: graphs   Node: efc70c625856

Provenance: formalization of a published result. Source: arXiv:2610.36895 Definition 1.1 and 2.1

A digraph D is unilaterally 2-linked if for every four pairwise distinct vertices s₁, t₁, s₂, t₂ in D, there exist vertex-disjoint directed paths P₁ and P₂ such that P₁ connects {s₁, t₁} (in either direction) and P₂ connects {s₂, t₂} (in either direction).
-/

/-- A digraph is unilaterally 2-linked if every four distinct terminals have vertex-disjoint paths in some orientation. -/
def digraph_is_unilaterally_two_linked {V : Type*} (D : Digraph V) : Prop :=
  ∀ (s₁ t₁ s₂ t₂ : V),
    [s₁, t₁, s₂, t₂].Nodup →
      ∃ (p₁ p₂ : List V),
        (digraph_is_directed_path D p₁ s₁ t₁ ∨ digraph_is_directed_path D p₁ t₁ s₁) ∧
        (digraph_is_directed_path D p₂ s₂ t₂ ∨ digraph_is_directed_path D p₂ t₂ s₂) ∧
        p₁.Disjoint p₂
