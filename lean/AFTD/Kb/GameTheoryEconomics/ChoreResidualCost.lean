import AFTD.Prelude

/-!
# chore_residual_cost

Topic: fair_division   Node: 27c5ccdafaf1

Provenance: formalization of a published result. Source: arXiv:2611.07468 Def. 2.1

Given a type α with decidable equality, a cost function c : α → NNReal taking values in the non-negative reals, a natural number k : ℕ, and a bundle S : Finset α, the k-chore residual cost chore_residual_cost c k S is defined as the supremum in NNReal over all sub-bundles T in the subtype {T : Finset α // T ⊆ S ∧ T.card = min k S.card} of the remaining cost ∑ x ∈ S \ T.val, c x.
-/

/-- The k-chore residual cost of a bundle S under additive cost c: the maximum cost of S after removing min(k, |S|) chores. -/
noncomputable def chore_residual_cost {α : Type*} [DecidableEq α] (c : α → NNReal) (k : ℕ) (S : Finset α) : NNReal := ⨆ T : {T : Finset α // T ⊆ S ∧ T.card = min k S.card}, ∑ x ∈ S \ T.val, c x
