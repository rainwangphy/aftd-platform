import AFTD.Prelude

/-!
# op1957_degree_gap_arithmetic

Topic: graphs   Node: 7367bfa3309a

Provenance: helper lemma. OP-1957; unbounded degree-gap counting, experiment 40104.

The proposed gap argument supplies the cut matching, residual matching and component-size inequalities.
-/

theorem op1957_degree_gap_arithmetic
    (k r g t s q h j nC nR z p ell : ℕ)
    (hr : 2 ≤ r) (hg : g < 2*r) (ht : r+1 ≤ t) (htgap : r+g ≤ t+1)
    (hkl : 2*t+r ≤ k) (hku : k ≤ 2*t+r+g)
    (hs : s+1 = t+r+h) (hq : t+1+s ≤ q)
    (hj : q+j = k) (hjpos : 1 ≤ j)
    (hC : nC = 2*k+r+h) (hR : nR+r+h = 2*k)
    (hz : 1 ≤ z) (hzj : z ≤ j)
    (hp : nC+2 = 2*p+q) (hell : p+ell = k) :
    h+j ≤ g ∧ z+1 ≤ 2*r+h ∧ nC < 3*(q+z)+z ∧
    2 ≤ q ∧ 2*p ≤ nC ∧ 2*ell+k ≤ nR := by
  omega
