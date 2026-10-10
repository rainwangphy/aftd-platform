import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticBosonicMulBosonic
import AFTD.Kb.Physics.FieldStatisticBosonicMulFermionic
import AFTD.Kb.Physics.FieldStatisticFermionicMulBosonic
import AFTD.Kb.Physics.FieldStatisticFermionicMulFermionic
import AFTD.Kb.Physics.FieldStatisticMulBosonic
import AFTD.Kb.Physics.FieldStatisticMulSelf
import AFTD.Kb.Physics.FieldStatisticFermionicNotEqBonsic
import AFTD.Kb.Physics.FieldStatisticNeqFermionicIffEqBosonic
import AFTD.Kb.Physics.FieldStatisticNeqBosonicIffEqFermionic
import AFTD.Kb.Physics.FieldStatisticBosonicNeIffFermionicEq
import AFTD.Kb.Physics.FieldStatisticFermionicNeIffBosonicEq
import AFTD.Kb.Physics.FieldStatisticOfListSingleton
import AFTD.Kb.Physics.FieldStatisticOfListFreeMonoid
import AFTD.Kb.Physics.FieldStatisticOfListEmpty
import AFTD.Kb.Physics.FieldStatisticOfListAppend
import AFTD.Kb.Physics.FieldStatisticOfListInsertionSort
import AFTD.Kb.Physics.FieldStatisticAddEqMul
import AFTD.Kb.Physics.FieldStatisticOfFinsetEmpty
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticInstFintype
import AFTD.Kb.Physics.FieldStatisticInstAddMonoid

/-!
# FieldSpecification

Topic: quantum_field_theory   Node: ffc56ef9f0a9

Provenance: formalization of a published result. Source: Physlib, `FieldSpecification`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldSpecification/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure `FieldSpecification` is defined to have the following content: - A type `Field` whose elements are the constituent fields of the theory. - For every field `f` in `Field`, a type `PositionLabel f` whose elements label the different position operators associated with the field `f`. For example, - For `f` a *real-scalar field*, `PositionLabel f` will have a unique element. - For `f` a *complex-scalar field*, `PositionLabel f` will have two elements, one for the field operator and one for its conjugate. - For `f` a *Dirac fermion*, `PositionLabel f` will have eight elements, one for each Lorentz index of the field and its conjugate. - For `f` a *Weyl fermion*, `PositionLabel f` will have four elements, one for each Lorentz index of the field and its conjugate. - For every field `f` in `Field`, a type `AsymptoticLabel f` whose elements label the different types of incoming asymptotic field operators associated with the field `f` (this also matches the types of outgoing asymptotic field operators). For example, - For `f` a *real-scalar field*, `AsymptoticLabel f` will have a unique element. - For `f` a *complex-scalar field*, `AsymptoticLabel f` will have two elements, one for the field operator and one for its conjugate. - For `f` a *Dirac fermion*, `AsymptoticLabel f` will have four elements, two for each spin. - For `f` a *Weyl fermion*, `AsymptoticLabel f` will have two elements, one for each spin. - For each field `f` in `Field`, a field statistic `statistic f` which classifies `f` as either `bosonic` or `fermionic`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The structure `FieldSpecification` is defined to have the following content: - A type `Field` whose elements are the constituent fields of the theory. - For every field `f` in `Field`, a type `PositionLabel f` whose elements label the different position operators associated with the field `f`. For example, - For `f` a *real-scalar field*, `PositionLabel f` will have a unique element. - For `f` a *complex-scalar field*, `PositionLabel f` will have two elements, one for the field operator and one for its conjugate. - For `f` a *Dirac fermion*, `PositionLabel f` will have eight elements, one for each Lorentz index of the field and its conjugate. - For `f` a *Weyl fermion*, `PositionLabel f` will have four elements, one for each Lorentz index of the field and its conjugate. - For every field `f` in `Field`, a type `AsymptoticLabel f` whose elements label the different types of incoming asymptotic field operators associated with the field `f` (this also matches the types of outgoing asymptotic field operators). For example, - For `f` a *real-scalar field*, `AsymptoticLabel f` will have a unique element. - For `f` a *complex-scalar field*, `AsymptoticLabel f` will have two elements, one for the field operator and one for its conjugate. - For `f` a *Dirac fermion*, `AsymptoticLabel f` will have four elements, two for each spin. - For `f` a *Weyl fermion*, `AsymptoticLabel f` will have two elements, one for each spin. - For each field `f` in `Field`, a field statistic `statistic f` which classifies `f` as either `bosonic` or `fermionic`. -/
structure FieldSpecification where
  /-- A type whose elements are the constituent fields of the theory. -/
  Field : Type
  /-- For every field `f` in `Field`, the type `PositionLabel f` has elements that label the
    different position operators associated with the field `f`. -/
  PositionLabel : Field → Type
  /-- For every field `f` in `Field`, the type `AsymptoticLabel f` has elements that label
    the different asymptotic based field operators associated with the field `f`. -/
  AsymptoticLabel : Field → Type
  /-- For every field `f` in `Field`, the field statistic `statistic f` classifies `f` as either
    `bosonic` or `fermionic`. -/
  statistic : Field → FieldStatistic
