import AFTD.Prelude
import AFTD.Kb.Optimization.IsSubmodularCube

/-!
# not_submodular_cube_three_two

Topic: submodular   Node: f8406dc89dd8

Provenance: helper lemma. arXiv:2611.02374, Sec. 1.2

For dimension n = 3 and range bound k = 2, the conjunction function x ↦ if x 0 ∧ x 1 then 1 else 0 is not submodular.
-/

/-- A conjunction function on {0, 1}^3 with range Fin 3 is not submodular. -/
theorem not_submodular_cube_three_two :
    ¬ is_submodular_cube (fun (x : Fin 3 → Bool) => (if x 0 && x 1 then (1 : Fin 3) else 0)) := by
  intro h
  have h_spec := h (fun i => i == 0) (fun i => i == 1)
  revert h_spec
  norm_num
