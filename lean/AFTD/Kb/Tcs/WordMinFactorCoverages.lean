import AFTD.Prelude
import AFTD.Kb.Tcs.WordFactorCoverages

/-!
# word_min_factor_coverages

Topic: combinatorics   Node: f4969222a4ce

Provenance: formalization of a published result. Source: arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Sec. 3.2.

H_min(w): the inclusion-minimal members of H(w), the family of factor coverages of w.
-/

/-- `H_min(w)`: the inclusion-minimal factor coverages of `w`. -/
def word_min_factor_coverages {α : Type*} [DecidableEq α] (w : List α) : Set (Finset ℕ) :=
  {C | C ∈ word_factor_coverages w ∧ ∀ D ∈ word_factor_coverages w, D ⊆ C → D = C}
