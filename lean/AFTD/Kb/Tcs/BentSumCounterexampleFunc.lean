import AFTD.Prelude

/-!
# bent_sum_counterexample_func

Topic: cryptography   Node: 2014f865393e

Provenance: formalization of a published result. Source: arXiv:2610.32239, Section 4.1, Eq. (4.3)

For any integer m ≥ 4, the Boolean function on (Fin (2 * m) → ZMod 2) defined by multiplying the first m - 2 coordinates and the sum of three disjoint quadratic terms on the next 6 coordinates.
-/

/-- The Boolean function f_n on (Fin (2 * m) → ZMod 2) for m ≥ 4, defined as the product of the first m - 2 variables times a 6-variable quadratic form. -/
def bent_sum_counterexample_func (m : ℕ) (hm : 4 ≤ m) (x : Fin (2 * m) → ZMod 2) : ZMod 2 :=
  (∏ i : Fin (m - 2), x ⟨i.val, by omega⟩) *
    (x ⟨m - 2, by omega⟩ * x ⟨m - 1, by omega⟩ +
     x ⟨m, by omega⟩ * x ⟨m + 1, by omega⟩ +
     x ⟨m + 2, by omega⟩ * x ⟨m + 3, by omega⟩)
