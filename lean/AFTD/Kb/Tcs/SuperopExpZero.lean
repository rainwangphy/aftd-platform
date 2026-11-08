import AFTD.Prelude
import AFTD.Kb.Tcs.SuperopExp

/-!
# superop_exp_zero

Topic: quantum   Node: 4701a4b55ffc

Provenance: helper lemma. sanity lemma for superop_exp

Sanity check: $e^{0 \cdot L}$ is the identity map.
-/

theorem superop_exp_zero (d : ℕ) (L : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) :
    superop_exp d L 0 = LinearMap.id := by
  simp [superop_exp]
