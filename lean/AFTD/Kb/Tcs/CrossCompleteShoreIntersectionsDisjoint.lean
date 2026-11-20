import AFTD.Prelude

/-!
# cross_complete_shore_intersections_disjoint

Topic: graphs   Node: 5cf9f6342c28

Provenance: helper lemma. Bridge-to-crossing-set verification for the OP-1957 campaign.

For two complete bipartite cross-shore pairs, the intersection of the W shores is disjoint from the union of the Q shores, and the intersection of the Q shores is disjoint from the union of the W shores.
-/

theorem cross_complete_shore_intersections_disjoint
    {V : Type*} [DecidableEq V] (H : SimpleGraph V)
    (W₁ W₂ Q₁ Q₂ : Finset V)
    (hcross₁ : ∀ q ∈ Q₁, ∀ w ∈ W₁, H.Adj q w)
    (hcross₂ : ∀ q ∈ Q₂, ∀ w ∈ W₂, H.Adj q w) :
    Disjoint (W₁ ∩ W₂) (Q₁ ∪ Q₂) ∧
      Disjoint (Q₁ ∩ Q₂) (W₁ ∪ W₂) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro w hw hq
    obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
    rcases Finset.mem_union.mp hq with hq₁ | hq₂
    · exact H.irrefl (hcross₁ w hq₁ w hw₁)
    · exact H.irrefl (hcross₂ w hq₂ w hw₂)
  · apply Finset.disjoint_left.mpr
    intro q hq hw
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_inter.mp hq
    rcases Finset.mem_union.mp hw with hw₁ | hw₂
    · exact H.irrefl (hcross₁ q hq₁ q hw₁)
    · exact H.irrefl (hcross₂ q hq₂ q hw₂)
