import AFTD.Prelude
import AFTD.Kb.NumberTheory.ForwardDiff

/-!
# iter_forward_diff

Topic: elementary_number_theory   Node: c1087dc9bd4f

Provenance: formalization of a published result. Source: arXiv:2611.26953, Section 1.1

For a natural number $k$ and a function $f : ℕ → ℤ$, the $k$-th iterated forward difference of $f$ is defined as the $k$-th iterate of the forward difference operator applied to $f$.
-/

/-- Iterated forward difference of an integer-valued function on the natural numbers. -/
def iter_forward_diff (k : ℕ) (f : ℕ → ℤ) : ℕ → ℤ := (forward_diff^[k]) f
