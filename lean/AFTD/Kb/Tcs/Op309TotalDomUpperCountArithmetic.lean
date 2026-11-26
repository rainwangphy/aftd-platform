import AFTD.Prelude

/-!
# op309_total_dom_upper_count_arithmetic

Topic: graphs   Node: 407bc040d93c

Provenance: helper lemma. OP-309 total edge domination counting.

The selected-component and boundary inequalities imply the cubic uncovered upper bound.
-/

theorem op309_total_dom_upper_count_arithmetic (n u c m : ℕ)
  (hn : n = u + c) (hboundary : 3*u + 2*m ≤ 3*c)
  (hcomponents : 2*c ≤ 3*m) : 14*u ≤ 5*n := by omega
