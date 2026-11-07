import AFTD.Prelude
import AFTD.Kb.Optimization.IsPStar
import AFTD.Kb.Optimization.IdentityIsPStarZero
import AFTD.Kb.Optimization.IsPStarKappa

/-!
# identity_is_p_star

Topic: lp_duality   Node: 9933ce8bdb45

Provenance: helper lemma. scout/2611-07815-newton-steps-are-faster-for-linear-complementarity-problems.md:219

For every dimension n : ℕ, the n-by-n real identity matrix indexed by Fin n belongs to the class P*.
-/

/-- The n-by-n identity matrix belongs to the class P*. -/
theorem identity_is_p_star (n : ℕ) : is_p_star n 1 := ⟨0, le_refl 0, identity_is_p_star_zero n⟩
