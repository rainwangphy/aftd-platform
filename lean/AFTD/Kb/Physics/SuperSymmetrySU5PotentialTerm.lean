import AFTD.Prelude

/-!
# SuperSymmetry.SU5.PotentialTerm

Topic: quantum_field_theory   Node: 7043bf2ff606

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.PotentialTerm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relevant terms part of the superpotential and Kahler potential of the `SU(5)` SUSY GUT.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option backward.isDefEq.respectTransparency false in
/-- Relevant terms part of the superpotential and Kahler potential of the `SU(5)` SUSY GUT. -/
inductive SuperSymmetry.SU5.PotentialTerm
  /-- The term `μ 5Hu 5̄Hd` appearing in the super-potential. -/ | μ : PotentialTerm
  /-- The term `𝛽ᵢ 5̄Mⁱ5Hu` appearing in the super-potential. -/
  | β : PotentialTerm
  /-- The term `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ` appearing in the super-potential. -/
  | Λ : PotentialTerm
  /-- The term `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` appearing in the super-potential. -/
  | W1 : PotentialTerm
  /-- The term `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd` appearing in the super-potential. -/
  | W2 : PotentialTerm
  /-- The term `W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu` appearing in the super-potential. -/
  | W3 : PotentialTerm
  /-- The term `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu` appearing in the super-potential. -/
  | W4 : PotentialTerm
  /-- The term `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ` appearing in the Kahler potential. -/
  | K1 : PotentialTerm
  /-- The term `K²ᵢ 5̄Hu 5̄Hd 10ⁱ` appearing in the Kahler potential. -/
  | K2 : PotentialTerm
  /-- The term `λᵗᵢⱼ 10ⁱ 10ʲ 5Hu` appearing in the super-potential. -/
  | topYukawa : PotentialTerm
  /-- The term `λᵇᵢⱼ 10ⁱ 5̄Mʲ 5̄Hd` appearing in the super-potential. -/
  | bottomYukawa : PotentialTerm
deriving DecidableEq, Fintype
