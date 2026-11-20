import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op309_girth34_peel_count_arithmetic

Topic: combinatorics   Node: 127aeef3e183

Provenance: helper lemma. OP-309 high-girth overlap-peeling density reduction, IN-1099.

The displayed block, class, host-edge, peeling-potential and girth-34 cycle-budget hypotheses imply 9p+38s+38z ≤ 291u and n ≤ 98u.
-/

theorem op309_girth34_peel_count_arithmetic
    (n p s z u q t k : Nat)
    (hvertices : n = 3*p + 4*s + 4*z + u)
    (hclass : 2*q + 2*s = p + 2*z + 3*u + 2*t)
    (hpeel : 3*p + s + 6*z + 3*u ≤ 5*q)
    (hhost : 2*k + 3*u = 5*p + 6*s + 6*z)
    (hcycles : 34*t ≤ 34*s + k) :
    9*p + 38*s + 38*z ≤ 291*u ∧ n ≤ 98*u := by
  constructor <;> nlinarith
