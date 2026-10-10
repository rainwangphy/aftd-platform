import AFTD.Prelude

/-!
# SuperSymmetry.SU5.ChargeSpectrum

Topic: quantum_field_theory   Node: 106c2359d0f2

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.ChargeSpectrum`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type such that an element corresponds to the collection of charges associated with the matter content of the theory. The order of charges is implicitly taken to be `qHd`, `qHu`, `Q5`, `Q10`. The `Q5` and `Q10` charges are represented by `Finset` rather than `Multiset`, so multiplicity is not included. This is defined for a general type `𝓩`, which could be e.g. - `ℤ` in the case of `U(1)`, - `ℤ × ℤ` in the case of `U(1) × U(1)`, - `Fin 2` in the case of `ℤ₂` etc.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type such that an element corresponds to the collection of charges associated with the matter content of the theory. The order of charges is implicitly taken to be `qHd`, `qHu`, `Q5`, `Q10`. The `Q5` and `Q10` charges are represented by `Finset` rather than `Multiset`, so multiplicity is not included. This is defined for a general type `𝓩`, which could be e.g. - `ℤ` in the case of `U(1)`, - `ℤ × ℤ` in the case of `U(1) × U(1)`, - `Fin 2` in the case of `ℤ₂` etc. -/
structure SuperSymmetry.SU5.ChargeSpectrum (𝓩 : Type := ℤ) where
  /-- The charge of the `Hd` particle. -/
  qHd : Option 𝓩
  /-- The negative of the charge of the `Hu` particle. That is to say,
    the charge of the `Hu` when considered in the 5-bar representation. -/
  qHu : Option 𝓩
  /-- The finite set of charges of the matter fields in the `Q5` representation. -/
  Q5 : Finset 𝓩
  /-- The finite set of charges of the matter fields in the `Q10` representation. -/
  Q10 : Finset 𝓩
