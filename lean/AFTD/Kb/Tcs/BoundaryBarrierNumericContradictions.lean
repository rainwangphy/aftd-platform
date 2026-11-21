import AFTD.Prelude

/-!
# boundary_barrier_numeric_contradictions

Topic: graphs   Node: b46680aad0cd

Provenance: helper lemma. OP-1957; arithmetic from the all-k saturated-block barrier route, experiment 36985.

The displayed cardinality and degree-defect constraints yield the four separator, lower-bound, degree-budget, and factor-critical matching-budget inequalities used in the saturated-block boundary reduction.
-/

theorem boundary_barrier_numeric_contradictions
    (k a b c s u t l v : ℕ)
    (ha : 3 ≤ a) (hc : c ≤ k) (hab : a+b=2*k)
    (hs : s ≤ u) (hdef : u+t+3 ≤ c) (hsize : l+v+s+t+2=2*k) :
    (0 < v → 2*k-c+s+2+t < 2*k) ∧
    (v=0 → 2*k-c+1 ≤ l) ∧
    (v=0 → 0<t → c-3 < l+1) ∧
    (v=0 → t=0 → b < l+s) := by
  omega
