import AFTD.Prelude
import AFTD.Kb.Tcs.AcceptingCount

/-!
# explicitError

Topic: circuits   Node: 8878c5a8bcbd

Provenance: formalization of a published result. Source: arXiv:2610.19174, Listing A.13

The explicit torus approximation error: 2^{-n-1} if the number of accepting inputs of f is odd, and 0 if even.
-/

/-- The explicit error bound 2^{-n-1} when acceptingCount is odd, and 0 when even. -/
noncomputable def explicitError {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ := if Odd (acceptingCount f) then 1 / (2 : ℝ) ^ (n + 1) else 0
