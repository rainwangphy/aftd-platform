import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OrderTop

/-!
# satisfies_majority_criterion

Topic: social_choice   Node: 1fabddde115a

Provenance: formalization of a published result. Source: arXiv:2611.26224 Sec. 5.2, p. 10

A voting rule f satisfies the majority criterion if it selects alternative x whenever strictly more than half of the voters rank x first.
-/

/-- A voting rule satisfies the majority criterion if it elects an alternative ranked first by more than half the voters. -/
def satisfies_majority_criterion {N A : Type*} [Fintype N] [Fintype A] [Nonempty A]
    (f : (N → LinearOrder A) → A) : Prop :=
  ∀ (P : N → LinearOrder A) (x : A),
    Fintype.card N < 2 * (Finset.filter (fun i => order_top (P i) = x) Finset.univ).card →
    f P = x
