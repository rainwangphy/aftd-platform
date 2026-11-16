import AFTD.Prelude

/-!
# capped_value

Topic: fair_division   Node: 52574defcf8a

Provenance: formalization of a published result. Source: arXiv:2611.15582, Section 3.1

For a valuation v on goods, a threshold t, and a finite set of goods R, the capped value c_t(R) is the sum over all goods g in R of min(v(g), t).
-/

/-- The capped value c_t(R) of a set of goods R with threshold t: the sum of min(v(g), t) over all g in R. -/
def capped_value {Good : Type*} (v : Good → ℝ) (t : ℝ) (R : Finset Good) : ℝ := ∑ g ∈ R, min (v g) t
