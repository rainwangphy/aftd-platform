import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasObviousGroupManipulation

/-!
# is_k_nomg

Topic: social_choice   Node: 7bfd2baf5950

Provenance: formalization of a published result. Source: arXiv:2611.26224 Sec. 5.3, p. 11

A voting rule f : (N → LinearOrder A) → A is k-NOMG if no nonempty coalition C : Finset N with card at most k has an obvious group manipulation by any misreport at any profile of linear orders.
-/

/-- Immunity to obvious group manipulation by coalitions of size at most k (k-NOMG). -/
def is_k_nomg {N A : Type*} (f : (N → LinearOrder A) → A) (k : ℕ) : Prop :=
  ∀ (C : Finset N), C.Nonempty → C.card ≤ k →
    ¬ ∃ (P P_dev : N → LinearOrder A), has_obvious_group_manipulation f C P P_dev
