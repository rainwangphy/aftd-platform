import AFTD.Prelude

/-!
# op309_triangle_free_host_rank_arithmetic

Topic: combinatorics   Node: 2c6aafe693ba

Provenance: helper lemma. OP-309 padded port-class incidence route; triangle-free host counting reduction, IN-1099.

If the stated cubic edge counts, selected-component counts, incidence-rank identity and triangle-free host cycle budget hold, the incidence rank is at least one plus one sixteenth of the graph order, with a stronger component-sensitive bound.
-/

theorem op309_triangle_free_host_rank_arithmetic (n m r k p s z u cyclic rank : ℕ) (hvertices : n = 3*p + 4*s + 4*z + u) (hselected : r = 2*p + 3*s + 3*z) (hcubic : 2*m = 3*n) (heven : n % 2 = 0) (hhost : k + r + 3*u = m) (hrank : rank + cyclic = n/2 + 1) (hcycles : cyclic ≤ s + k/4) : 8 + 7*p + 2*s + 10*z + 7*u ≤ 8*rank ∧ 16 + n ≤ 16*rank := by constructor <;> omega
