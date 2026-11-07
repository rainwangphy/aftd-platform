import AFTD.Prelude

/-!
# chvatal_hanson_bound

Topic: graphs   Node: d12bd4981794

Provenance: formalization of a published result. Source: arXiv:2611.01259 eq. (12)

For natural numbers D and M, the Chvátal-Hanson edge bound on ℕ is D * M + (D / 2) * (M / ((D + 1) / 2)), using truncated natural number division.
-/

/-- The Chvátal-Hanson bound on the number of edges under degree and matching constraints. -/
def chvatal_hanson_bound (D M : ℕ) : ℕ := D * M + (D / 2) * (M / ((D + 1) / 2))
