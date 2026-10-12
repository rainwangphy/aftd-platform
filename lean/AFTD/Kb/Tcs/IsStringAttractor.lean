import AFTD.Prelude
import AFTD.Kb.Tcs.WordOccurrenceCoverage

/-!
# is_string_attractor

Topic: combinatorics   Node: ada396697c84

Provenance: formalization of a published result. Source: arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Definition 3.1. Factor = contiguous sublist (List.IsInfix).

A set Γ ⊆ [1, |w|] of positions is a string attractor of the finite word w if Γ ∩ Cov_w(x) ≠ ∅ for every nonempty factor x of w.
-/

/-- `Γ` is a string attractor of `w`: a set of (1-based) positions of `w` meeting the coverage of every nonempty factor of `w`. -/
def is_string_attractor {α : Type*} [DecidableEq α] (w : List α) (Γ : Finset ℕ) : Prop :=
  Γ ⊆ Finset.Icc 1 w.length ∧
    ∀ x : List α, x ≠ [] → x <:+: w → (Γ ∩ word_occurrence_coverage w x).Nonempty
