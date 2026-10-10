import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorClauseNodeColor

/-!
# lorentzAlgebra.rotationGenerator

Topic: special_relativity   Node: d4890cde2394

Provenance: formalization of a published result. Source: Physlib, `lorentzAlgebra.rotationGenerator`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzAlgebra/Basis.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The rotation generator J_i in the Lorentz algebra so(1,3). This matrix generates infinitesimal rotations about the i-th axis following the right-hand rule. The matrix acts only on spatial indices in the antisymmetric pattern characteristic of angular momentum generators. ## Properties - Antisymmetric: J_iᵀ = -J_i - Traceless: tr(J_i) = 0 - Satisfies Lorentz algebra condition: J_iᵀ η = -η J_i ## Structure - J_0 (rotation about x-axis) : Acts on (y,z) components - J_1 (rotation about y-axis) : Acts on (z,x) components - J_2 (rotation about z-axis) : Acts on (x,y) components ## Physical Meaning Exponentiating θ·J_i produces a finite rotation by angle θ about axis i.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The rotation generator J_i in the Lorentz algebra so(1,3). This matrix generates infinitesimal rotations about the i-th axis following the right-hand rule. The matrix acts only on spatial indices in the antisymmetric pattern characteristic of angular momentum generators. ## Properties - Antisymmetric: J_iᵀ = -J_i - Traceless: tr(J_i) = 0 - Satisfies Lorentz algebra condition: J_iᵀ η = -η J_i ## Structure - J_0 (rotation about x-axis) : Acts on (y,z) components - J_1 (rotation about y-axis) : Acts on (z,x) components - J_2 (rotation about z-axis) : Acts on (x,y) components ## Physical Meaning Exponentiating θ·J_i produces a finite rotation by angle θ about axis i. -/
def lorentzAlgebra.rotationGenerator (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  fun μ ν =>
    match i with
    | 0 => if μ = Sum.inr 1 ∧ ν = Sum.inr 2 then -1
            else if μ = Sum.inr 2 ∧ ν = Sum.inr 1 then 1
            else 0
      | 1 => if μ = Sum.inr 0 ∧ ν = Sum.inr 2 then 1
            else if μ = Sum.inr 2 ∧ ν = Sum.inr 0 then -1
            else 0
      | 2 => if μ = Sum.inr 0 ∧ ν = Sum.inr 1 then -1
            else if μ = Sum.inr 1 ∧ ν = Sum.inr 0 then 1
            else 0
