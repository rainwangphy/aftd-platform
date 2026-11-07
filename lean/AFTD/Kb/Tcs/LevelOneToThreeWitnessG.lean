import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# level_one_to_three_witness_g

Topic: combinatorics   Node: 5a95e4eb982b

Provenance: helper lemma. step towards discrete_level_one_to_three_lower_bound_three_vars

The second witness function of the three-variable example of arXiv:2611.08289 equation (53): g(x) = -(sigma(x_0) + sigma(x_1) + sigma(x_2) - sigma(x_0)sigma(x_1)sigma(x_2)) = -chi_{0} - chi_{1} - chi_{2} + chi_{012}, where sigma = boolToSign.
-/

/-- The witness g = -chi_{0} - chi_{1} - chi_{2} + chi_{012} of the three-variable example, written in sign encoding. -/
noncomputable def level_one_to_three_witness_g : BooleanAnalysis.BooleanFunc 3 := fun x =>
  -((BooleanAnalysis.boolToSign (x 0) + BooleanAnalysis.boolToSign (x 1) + BooleanAnalysis.boolToSign (x 2)) -
    BooleanAnalysis.boolToSign (x 0) * BooleanAnalysis.boolToSign (x 1) * BooleanAnalysis.boolToSign (x 2))
