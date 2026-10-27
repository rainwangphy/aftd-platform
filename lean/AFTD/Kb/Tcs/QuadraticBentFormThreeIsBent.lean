import AFTD.Prelude
import AFTD.Kb.Tcs.IsBent

/-!
# quadratic_bent_form_three_is_bent

Topic: cryptography   Node: 5356e98416e1

Provenance: helper lemma. arXiv:2610.32239, Lemma 4.1

The standard quadratic form on (Fin 6 → ZMod 2) given by z 0 * z 1 + z 2 * z 3 + z 4 * z 5 is bent.
-/

/-- The quadratic form z₁z₂ + z₃z₄ + z₅z₆ on 6 variables is a bent function. -/
theorem quadratic_bent_form_three_is_bent :
    is_bent (fun z : Fin 6 → ZMod 2 => z 0 * z 1 + z 2 * z 3 + z 4 * z 5) := by
  unfold is_bent
  decide
