import AFTD.Prelude

/-!
# op309_incidence_weighted_four_peel

Topic: graphs   Node: 62e75a62e58e

Provenance: helper lemma. OP-309 weighted-four shortcut examined in IN-1099.

Every nonempty subset of classes contains a class with at most four counted host incidences.
-/

def op309_incidence_weighted_four_peel {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj] : Prop := ∀ S : Finset A, S.Nonempty → ∃ a ∈ S, (∑ b : B, if I.Adj (.inl a) (.inr b) then (S.filter fun a' => I.Adj (.inl a') (.inr b)).card - 1 else 0) ≤ 4
