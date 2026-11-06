import AFTD.Prelude

/-!
# anti_ribbon_diagram

Topic: combinatorics   Node: f0eb1cefab54

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 2.2

For a positive integer N and a descent set S : Finset ℕ, the anti-ribbon diagram anti_ribbon_diagram N S is the finite set of cells in ℕ × ℕ indexed by k ∈ {1, ..., N}, starting at p₁ = (1, 1), where the k-th cell has row coordinate 1 + |{i ∈ S | 1 ≤ i < k}| and column coordinate 1 + (k - 1 - |{i ∈ S | 1 ≤ i < k}|).
-/

/-- The anti-ribbon diagram of size N associated with a descent set S. -/
def anti_ribbon_diagram (N : ℕ) (S : Finset ℕ) : Finset (ℕ × ℕ) := (Finset.Icc 1 N).image fun k =>
  (1 + ((Finset.Ico 1 k).filter (· ∈ S)).card,
   1 + (k - 1 - ((Finset.Ico 1 k).filter (· ∈ S)).card))
