import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystem
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemUnitaryRelation
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstNormedAddCommGroupHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstInnerProductSpaceComplexHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstCompleteSpaceHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstZero

/-!
# QuantumMechanics.QuantumSystem.unitaryRelation_symm

Topic: quantum_mechanics   Node: 436a379b8ec0

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.QuantumSystem.unitaryRelation_symm`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/QuantumSystem/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `UnitaryRelation` is symmetric.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
/-- The relation `UnitaryRelation` is symmetric. -/
lemma QuantumMechanics.QuantumSystem.unitaryRelation_symm {Q₁ Q₂ : QuantumSystem} (h₁₂ : UnitaryRelation Q₁ Q₂) :
    UnitaryRelation Q₂ Q₁ := by
  obtain ⟨e, h_domain, h⟩ := h₁₂
  refine ⟨e.symm, by ext; simp [← h_domain], fun ψ₂ ↦ ?_⟩
  apply e.symm_apply_eq.mpr
  simp [h ⟨e.symm ψ₂, by simpa [← h_domain] using ψ₂.2⟩]
