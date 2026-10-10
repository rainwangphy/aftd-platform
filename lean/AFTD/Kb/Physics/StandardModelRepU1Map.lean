import AFTD.Prelude

/-!
# StandardModel.repU1Map

Topic: quantum_field_theory   Node: 815f8a6ef5a5

Provenance: formalization of a published result. Source: Physlib, `StandardModel.repU1Map`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Representations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The 2d representation of U(1) with charge 3 as a map from U(1) to `unitaryGroup (Fin 2) ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The 2d representation of U(1) with charge 3 as a map from U(1) to `unitaryGroup (Fin 2) ℂ`. -/
@[simps!]
noncomputable def StandardModel.repU1Map (g : unitary ℂ) : unitaryGroup (Fin 2) ℂ :=
  ⟨g ^ 3 • 1, by
    rw [mem_unitaryGroup_iff, smul_one_mul, show g = ⟨g.1, g.prop⟩ from rfl]
    simp only [SubmonoidClass.mk_pow, Submonoid.mk_smul, star_smul, star_pow, RCLike.star_def,
      star_one]
    rw [smul_smul, ← mul_pow]
    rw [← star_def, (Unitary.mem_iff.mp g.prop).2]
    simp only [one_pow, one_smul]⟩
