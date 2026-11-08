import AFTD.Prelude

/-!
# is_dominating_distribution

Topic: online_algorithms   Node: 72bfb27c6f6a

Provenance: formalization of a published result. Source: arXiv:2610.40824 Definition 6, eq. (2)

A probability distribution μ on Fin n supported on cache C is dominating with respect to pairwise hitting probabilities α if for every resident page q in C, the expected probability that a page drawn from μ is requested before q is at most 1/2.
-/

/-- A distribution μ supported on C is dominating if ∑_{p ∈ C} μ(p) α(p, q) ≤ 1/2 for all q ∈ C. -/
def is_dominating_distribution {n : ℕ} (C : Finset (Fin n))
    (α : Fin n → Fin n → ℝ) (μ : Fin n → ℝ) : Prop := (∀ p, 0 ≤ μ p) ∧
  (∑ p, μ p = 1) ∧
  (∀ p, p ∉ C → μ p = 0) ∧
  (∀ q ∈ C, ∑ p ∈ C, μ p * α p q ≤ 1 / 2)
