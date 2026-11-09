import AFTD.Prelude

/-!
# ballot_weight

Topic: combinatorics   Node: 98f4e7e79440

Provenance: formalization of a published result. Source: arXiv:2611.06860 "Largest Sperner families with bounded VC-dimension", Section 2, above Lemma 2.5

The function ballot_weight taking two natural numbers $p$ and $k$ and returning the natural number defined as: if $k = 0$ then $\binom{p}{0}$, and otherwise the natural number difference $\binom{p}{k} - \binom{p}{k-1}$.
-/

/-- The ballot weight b(p, k) as a natural number: p.choose 0 if k = 0, else p.choose k - p.choose (k - 1). -/
def ballot_weight (p k : ℕ) : ℕ := if k = 0 then p.choose 0 else p.choose k - p.choose (k - 1)
