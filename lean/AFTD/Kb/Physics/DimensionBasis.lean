import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionExponentCoeInj
import AFTD.Kb.Physics.DimensionExponentCoeZero
import AFTD.Kb.Physics.DimensionExponentCoeOne
import AFTD.Kb.Physics.DimensionExponentCoeOfNat
import AFTD.Kb.Physics.DimensionExponentCoeAdd
import AFTD.Kb.Physics.DimensionExponentCoeSub
import AFTD.Kb.Physics.DimensionExponentCoeNeg
import AFTD.Kb.Physics.DimensionExponentCoeMul
import AFTD.Kb.Physics.DimensionExponentCoeInv
import AFTD.Kb.Physics.DimensionExponentCoeDiv
import AFTD.Kb.Physics.DimensionExponentCoeLeCoe
import AFTD.Kb.Physics.DimensionExponentCoeLtCoe
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstMul
import AFTD.Kb.Physics.DimensionExponentInstInv
import AFTD.Kb.Physics.DimensionExponentInstDiv
import AFTD.Kb.Physics.DimensionExponentInstField
import AFTD.Kb.Physics.DimensionExponentInstCoeRat
import AFTD.Kb.Physics.DimensionExponentInstLinearOrder
import AFTD.Kb.Physics.DimensionExponentInstIsStrictOrderedRing
import AFTD.Kb.Physics.DimensionExponentInstCharZero

/-!
# DimensionBasis

Topic: classical_mechanics   Node: 140ff016a99c

Provenance: formalization of a published result. Source: Physlib, `DimensionBasis`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Dimension.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

A choice of exponent-tuple representation for a basis `B`. Native addition on `Exponents` is used for dimension multiplication, while `exponentEquiv` provides the basis-generic API.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A choice of exponent-tuple representation for a basis `B`. Native addition on `Exponents` is used for dimension multiplication, while `exponentEquiv` provides the basis-generic API. -/
class DimensionBasis (B : Type) where
  /-- The native tuple of exponents for this basis. -/
  Exponents : Type
  /-- The additive structure on native exponent tuples. -/
  [addCommGroup : AddCommGroup Exponents]
  /-- Native exponent tuples are additively equivalent to exponent functions on the basis. -/
  exponentEquiv : Exponents ≃+ (B → Dimension.Exponent)

attribute [instance_reducible, instance] DimensionBasis.addCommGroup
