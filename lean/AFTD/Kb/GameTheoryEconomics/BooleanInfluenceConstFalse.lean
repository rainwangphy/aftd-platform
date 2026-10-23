import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BooleanInfluence
import AFTD.Kb.GameTheoryEconomics.BooleanProductBernoulli

/-!
# boolean_influence_const_false

Topic: combinatorial_games   Node: 30ae2aef6ace

Provenance: helper lemma. arXiv:2610.30730 Section 2

For any finite type $U$ with decidable equality, coordinate $i \in U$, and parameter $p$ in `unitInterval`, the influence of coordinate $i$ on the constant false function `fun _ => false` under `boolean_influence` is 0.
-/

/-- Sanity lemma: the constant false function has zero influence at every coordinate. -/
lemma boolean_influence_const_false (U : Type*) [Fintype U] [DecidableEq U]
    (i : U) (p : unitInterval) :
    boolean_influence U (fun _ ↦ false) i p = 0 := by
  unfold boolean_influence
  simp
