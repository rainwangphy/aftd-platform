import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_is_two_linked

Topic: graphs   Node: 418a4b7602cb

Provenance: formalization of a published result. Source: arXiv:2610.36895 Sec. 1

A digraph D is 2-linked if for every four pairwise distinct vertices s₁, t₁, s₂, t₂ in D, there exist vertex-disjoint directed paths from s₁ to t₁ and from s₂ to t₂.
-/

/-- A digraph is 2-linked if every four distinct terminals have vertex-disjoint directed paths. -/
def digraph_is_two_linked {V : Type*} (D : Digraph V) : Prop :=
  ∀ (s₁ t₁ s₂ t₂ : V),
    [s₁, t₁, s₂, t₂].Nodup →
      ∃ (p₁ p₂ : List V),
        digraph_is_directed_path D p₁ s₁ t₁ ∧
        digraph_is_directed_path D p₂ s₂ t₂ ∧
        p₁.Disjoint p₂
