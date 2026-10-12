import AFTD.Prelude
import AFTD.Kb.Tcs.WordOccurrenceCoverage

/-!
# word_factor_coverages

Topic: combinatorics   Node: 72876ab87797

Provenance: formalization of a published result. Source: arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Sec. 3.2.

H(w): the family of coverages Cov_w(x) of the nonempty factors x of w.
-/

/-- `H(w)`: the coverages of the nonempty factors of `w`. -/
def word_factor_coverages {α : Type*} [DecidableEq α] (w : List α) : Set (Finset ℕ) :=
  {C | ∃ x : List α, x ≠ [] ∧ x <:+: w ∧ word_occurrence_coverage w x = C}
