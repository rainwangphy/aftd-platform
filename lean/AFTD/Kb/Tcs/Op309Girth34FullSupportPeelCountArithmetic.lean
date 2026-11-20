import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op309_girth34_full_support_peel_count_arithmetic

Topic: combinatorics   Node: 61de7b9f5c7c

Provenance: helper lemma. OP-309 high-girth overlap-peeling density reduction, IN-1099.

The displayed block, class, full-host-edge, peeling-potential and girth-34 cycle-budget hypotheses imply 9p+38s+38z ≤ 321u and n ≤ 108u.
-/

theorem op309_girth34_full_support_peel_count_arithmetic
    (n p s z u q t k : Nat)
    (hvertices : n = 3*p + 4*s + 4*z + u)
    (hclass : 2*q + 2*s = p + 2*z + 3*u + 2*t)
    (hpeel : 3*p + s + 6*z + 3*u ≤ 5*q)
    (hhost : 2*k = 5*p + 6*s + 6*z + 3*u)
    (hcycles : 34*t ≤ 34*s + k) :
    9*p + 38*s + 38*z ≤ 321*u ∧ n ≤ 108*u := by
  constructor <;> nlinarith
