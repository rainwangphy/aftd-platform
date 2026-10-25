import AFTD.Prelude
import AFTD.Kb.Tcs.Monomial

/-!
# reed_muller_code

Topic: quantum   Node: fe127e4ee00a

Provenance: formalization of a published result. Source: arXiv:2610.09341, Appendix A.1; MacWilliams and Sloane (1977), Ch. 13

For natural numbers r and s, the binary Reed-Muller code RM(r, s) is the submodule of Boolean functions from (Fin s → ZMod 2) to ZMod 2 spanned by all monomials associated with subsets of Fin s of cardinality at most r.
-/

/-- The Reed-Muller code RM(r, s) over ZMod 2, defined as the subspace of Boolean functions spanned by monomials of degree at most r. -/
def reed_muller_code (r s : ℕ) : Submodule (ZMod 2) ((Fin s → ZMod 2) → ZMod 2) := Submodule.span (ZMod 2) { f | ∃ (T : Finset (Fin s)), T.card ≤ r ∧ f = monomial T }
