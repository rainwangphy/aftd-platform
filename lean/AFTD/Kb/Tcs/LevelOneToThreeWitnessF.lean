import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# level_one_to_three_witness_f

Topic: combinatorics   Node: a18824e3a01a

Provenance: helper lemma. step towards discrete_level_one_to_three_lower_bound_three_vars

The first witness function of the three-variable example of arXiv:2611.08289 equation (53): f(x) = -(sigma(x_0) + sigma(x_1) + sigma(x_2) + sigma(x_0)sigma(x_1)sigma(x_2)) = -chi_{0} - chi_{1} - chi_{2} - chi_{012}, where sigma = boolToSign is the sign encoding (false -> 1, true -> -1).
-/

/-- The witness f = -chi_{0} - chi_{1} - chi_{2} - chi_{012} of the three-variable example, written in sign encoding. -/
noncomputable def level_one_to_three_witness_f : BooleanAnalysis.BooleanFunc 3 := fun x =>
  -((BooleanAnalysis.boolToSign (x 0) + BooleanAnalysis.boolToSign (x 1) + BooleanAnalysis.boolToSign (x 2)) +
    BooleanAnalysis.boolToSign (x 0) * BooleanAnalysis.boolToSign (x 1) * BooleanAnalysis.boolToSign (x 2))
