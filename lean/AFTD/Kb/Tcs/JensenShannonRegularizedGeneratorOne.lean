import AFTD.Prelude
import AFTD.Kb.Tcs.JensenShannonRegularizedGenerator
import AFTD.Kb.Tcs.JensenShannonGenerator

/-!
# jensen_shannon_regularized_generator_one

Topic: information   Node: c742e8d2ee38

Provenance: helper lemma. folklore

For any parameter c, the regularized generator evaluates to 0 at 1: f_c(1) = 0.
-/

/-- The regularized generator satisfies f_c(1) = 0. -/
theorem jensen_shannon_regularized_generator_one (c : ℝ) :
    jensen_shannon_regularized_generator c 1 = 0 := by
  unfold jensen_shannon_regularized_generator jensen_shannon_generator
  norm_num
