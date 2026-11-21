import AFTD.Prelude

/-!
# boundary_one_barrier_count_impossible

Topic: graphs   Node: 67236aeb9d54

Provenance: helper lemma. OP-1957: arithmetic for a one-vertex barrier in the nonclique four-block route.

The displayed nonnegative integer block counts, odd extra-shore size, residual size and endpoint and extra-shore defect inequalities are inconsistent.
-/

theorem boundary_one_barrier_count_impossible
    (k a b c d e f g h i j l m t : ℕ) (hk : 5 ≤ k)
    (ha : 1 ≤ a) (hg : 1 ≤ g) (hu : i+j+l+m=2*t+1)
    (htotal : a+b+c+d+e+f+g+h+i+j+l+m+1=2*k)
    (hA : a+e+i ≤ 5) (hC : c+g+l ≤ 5)
    (hB : b+f+j+5 ≤ 2*k) (hD : d+h+m+5 ≤ 2*k)
    (hx : e+i+g+l+h+m ≤ 3) (hy : a+i+b+j+c+l ≤ 3)
    (hAi : 1 ≤ i → a+e+c+g+d+h ≤ 2)
    (hBj : 1 ≤ j → b+f+c+g+d+h+8 ≤ 2*k)
    (hCl : 1 ≤ l → a+e+b+f+c+g ≤ 2)
    (hDm : 1 ≤ m → a+e+b+f+d+h+8 ≤ 2*k) : False := by
  by_cases hi : 1 ≤ i <;> by_cases hj : 1 ≤ j <;>
    by_cases hl : 1 ≤ l <;> by_cases hm : 1 ≤ m <;>
    simp_all only [true_implies, false_implies] <;> omega
