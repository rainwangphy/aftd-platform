import AFTD.Prelude

/-!
# is_envy_free_coupling

Topic: social_choice   Node: b7752987cd03

Provenance: formalization of a published result. Source: arXiv:2405.03687, Section 4

Given n parties, vote shares p : Fin n → ℝ, house size H, and marginal distributions distH on k-subsets (where k = H - ∑ i, Nat.floor (H * p i)) and distH1 on k'-subsets (where k' = (H + 1) - ∑ i, Nat.floor ((H + 1) * p i)), is_envy_free_coupling p H distH distH1 prob asserts that prob is non-negative, the sum of prob S T over all size-k' subsets T equals distH S for each size-k subset S, and the sum of prob S T over all size-k subsets S equals distH1 T for each size-k' subset T.
-/

open Classical in
/-- A joint probability distribution is a coupling between two marginal lotteries at house sizes H and H + 1. -/
def is_envy_free_coupling {n : ℕ} (p : Fin n → ℝ) (H : ℕ)
    (distH distH1 : Finset (Fin n) → ℝ)
    (prob : Finset (Fin n) → Finset (Fin n) → ℝ) : Prop :=
  let k := H - ∑ i, Nat.floor (H * p i)
  let k' := (H + 1) - ∑ i, Nat.floor ((H + 1) * p i)
  (∀ S T, 0 ≤ prob S T) ∧
  (∀ S ∈ Finset.powersetCard k Finset.univ,
    ∑ T ∈ Finset.powersetCard k' Finset.univ, prob S T = distH S) ∧
  (∀ T ∈ Finset.powersetCard k' Finset.univ,
    ∑ S ∈ Finset.powersetCard k Finset.univ, prob S T = distH1 T)
