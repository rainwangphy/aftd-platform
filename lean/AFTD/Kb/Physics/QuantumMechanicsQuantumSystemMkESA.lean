import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsEssentiallySelfAdjoint
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystem
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointClosureEqAdjoint
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointAdjointEqClosure
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstNormedAddCommGroupHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstInnerProductSpaceComplexHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstCompleteSpaceHS
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId
import AFTD.Kb.Physics.LinearPMapIsUnbounded

/-!
# QuantumMechanics.QuantumSystem.mkESA

Topic: quantum_mechanics   Node: 3f70df5f2a69

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.QuantumSystem.mkESA`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/QuantumSystem/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Create a quantum system from a Hamiltonian operator which is merely essentially self-adjoint by taking its closure.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
/-- Create a quantum system from a Hamiltonian operator which is merely essentially self-adjoint by taking its closure. -/
noncomputable def QuantumMechanics.QuantumSystem.mkESA {HS : Type*} [NormedAddCommGroup HS] [InnerProductSpace ℂ HS] [CompleteSpace HS]
    {ℋ : HS →ₗ.[ℂ] HS} (hℋ : IsEssentiallySelfAdjoint ℋ) : QuantumSystem := ⟨HS, ℋ.closure, hℋ⟩
