import AFTD.Prelude

/-!
# lp_coord_refine

Topic: online_algorithms   Node: bc6ab00f6880

Provenance: formalization of a published result. Source: arXiv:2610.40824 Proposition 7 proof

Given a set S of distributions on Fin n and a list of page coordinates L, lp_coord_refine S L m is the subset of distributions obtained after m successive linear programming coordinate-maximization steps on L.
-/

/-- Successive coordinate-maximization steps refining feasible set S along page list L. -/
def lp_coord_refine {n : ℕ} (S : Set (Fin n → ℝ)) (L : List (Fin n)) : ℕ → Set (Fin n → ℝ)
| 0 => S
| m + 1 =>
  if h : m < L.length then
    { μ ∈ lp_coord_refine S L m | ∀ ν ∈ lp_coord_refine S L m, ν (L.get ⟨m, h⟩) ≤ μ (L.get ⟨m, h⟩) }
  else
    lp_coord_refine S L m
