import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterTightBindingChain
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValAdd
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValSmul
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValZero
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceNormEqVal
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInnerEqVal
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstAddCommGroup
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstModuleComplex
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstNormedAddCommGroup
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstInnerProductSpaceComplex
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstFiniteDimensionalComplex
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstCompleteSpace

/-!
# CondensedMatter.TightBindingChain.HilbertSpace

Topic: condensed_matter   Node: cdb5a15e96a8

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain.HilbertSpace`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Hilbert space of a `TightBindingchain` is the `N`-dimensional finite dimensional Hilbert space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open CondensedMatter in
open InnerProductSpace in
variable (T : TightBindingChain) in
/-- The Hilbert space of a `TightBindingchain` is the `N`-dimensional finite dimensional Hilbert space. -/
abbrev CondensedMatter.TightBindingChain.HilbertSpace := QuantumMechanics.FiniteHilbertSpace (Fin T.N)
