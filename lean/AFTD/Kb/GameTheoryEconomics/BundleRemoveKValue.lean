import AFTD.Prelude

/-!
# bundle_remove_k_value

Topic: fair_division   Node: b8c69119145d

Provenance: formalization of a published result. Source: arXiv:2610.34625, Section 2.1

Given a type of goods α with decidable equality, a valuation function v : Finset α → ℝ, a natural number k : ℕ, and a bundle S : Finset α, bundle_remove_k_value v k S is defined as the indexed infimum ⨅ X : {X : Finset α // X ⊆ S ∧ X.card ≤ k}, v (S \ X.val) over the subtype of sub-bundles X : Finset α satisfying X ⊆ S and X.card ≤ k.
-/

/-- The value of a bundle S after removing the k most valuable goods under valuation v, defined as the infimum of v(S \ X) over sub-bundles X ⊆ S with |X| ≤ k. -/
noncomputable def bundle_remove_k_value {α : Type*} [DecidableEq α] (v : Finset α → ℝ) (k : ℕ) (S : Finset α) : ℝ :=
  ⨅ X : {X : Finset α // X ⊆ S ∧ X.card ≤ k}, v (S \ X.val)
