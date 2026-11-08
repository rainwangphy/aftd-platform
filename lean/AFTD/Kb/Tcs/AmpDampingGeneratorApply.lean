import AFTD.Prelude
import AFTD.Kb.Tcs.AmpDampingGenerator
import AFTD.Kb.Tcs.PAmpDamping
import AFTD.Kb.Tcs.VAmpDamping

/-!
# amp_damping_generator_apply

Topic: quantum   Node: 5f0ba01cd3cb

Provenance: helper lemma. sanity lemma for amp_damping_generator (arXiv:2610.37187 eq. 7.1)

Sanity check: the generator acts as $G(X) = V X V^\dagger - \tfrac12(PX + XP)$.
-/

theorem amp_damping_generator_apply (d : ℕ) (h : 2 ≤ d) (X : Matrix (Fin d) (Fin d) ℂ) :
    amp_damping_generator d h X = v_amp_damping d h * X * star (v_amp_damping d h)
      - (1/2 : ℂ) • (p_amp_damping d h * X + X * p_amp_damping d h) := by
  simp [amp_damping_generator, mul_assoc]
