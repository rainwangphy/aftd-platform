import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op309_high_girth_peel_count_arithmetic

Topic: combinatorics   Node: 031f0d9106fa

Provenance: helper lemma. OP-309 high-girth overlap-peeling obstruction, IN-1099.

The displayed block, class, host-edge, peeling-potential and girth-26 cycle-budget hypotheses imply p+22s+22z ≤ 219u and n ≤ 658u.
-/

theorem op309_high_girth_peel_count_arithmetic
    (n p s z u q t k : Nat)
    (hvertices : n = 3*p + 4*s + 4*z + u)
    (hclass : 2*q + 2*s = p + 2*z + 3*u + 2*t)
    (hpeel : 3*p + s + 6*z + 3*u ≤ 5*q)
    (hhost : 2*k + 3*u = 5*p + 6*s + 6*z)
    (hcycles : 26*t ≤ 26*s + k) :
    p + 22*s + 22*z ≤ 219*u ∧ n ≤ 658*u := by
  constructor <;> nlinarith
