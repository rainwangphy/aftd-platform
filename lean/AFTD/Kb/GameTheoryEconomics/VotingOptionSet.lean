import AFTD.Prelude

/-!
# voting_option_set

Topic: social_choice   Node: fae099de1118

Provenance: formalization of a published result. Source: arXiv:2611.26224 Sec. 3, p. 4

Given a voting rule f : (N → LinearOrder A) → A, a finite coalition C : Finset N, and a profile P : N → LinearOrder A of linear orders on A, voting_option_set f C P is the set of all alternatives x : A such that there exists a profile P' : N → LinearOrder A agreeing with P on all members of C with f P' = x.
-/

/-- The option set of a coalition C at preference profile P under voting rule f. -/
def voting_option_set {N A : Type*} (f : (N → LinearOrder A) → A)
    (C : Finset N) (P : N → LinearOrder A) : Set A := { x : A | ∃ P' : N → LinearOrder A, (∀ i ∈ C, P' i = P i) ∧ f P' = x }
