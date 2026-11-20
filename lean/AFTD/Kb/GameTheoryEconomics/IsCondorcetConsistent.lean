import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinner

/-!
# is_condorcet_consistent

Topic: social_choice   Node: 7a6cd93c94ab

Provenance: formalization of a published result. Source: arXiv:2611.26224 Sec. 5.2, p. 10

A voting rule f : (N → LinearOrder A) → A on a finite voter set N is Condorcet-consistent if for every profile of linear orders P and alternative x, if x is a Condorcet winner at P then f P = x.
-/

/-- A voting rule is Condorcet-consistent if it selects the Condorcet winner whenever one exists. -/
def is_condorcet_consistent {N A : Type*} [Fintype N] (f : (N → LinearOrder A) → A) : Prop :=
  ∀ (P : N → LinearOrder A) (x : A), is_condorcet_winner P x → f P = x
