import AFTD.Prelude

/-!
# word_occurrence_coverage

Topic: combinatorics   Node: d19192e4fe82

Provenance: formalization of a published result. Source: arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Sec. 3.1, equation (1). Positions are 1-based as in the paper.

The coverage Cov_w(x) of a word x in a finite word w: the union of the intervals [p, p+|x|−1] over all (1-based) occurrence starts p of x in w, i.e. all p with w[p..p+|x|−1] = x.
-/

/-- Coverage of `x` in `w`: the union of the (1-based) intervals `[p, p+|x|-1]` over all starts `p` of occurrences of `x` in `w`. -/
def word_occurrence_coverage {α : Type*} [DecidableEq α] (w x : List α) : Finset ℕ :=
  ((Finset.Icc 1 w.length).filter (fun p => (w.drop (p - 1)).take x.length = x)).biUnion
    (fun p => Finset.Icc p (p + x.length - 1))
