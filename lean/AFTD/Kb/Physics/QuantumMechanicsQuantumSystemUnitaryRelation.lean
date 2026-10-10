import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystem
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstNormedAddCommGroupHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstInnerProductSpaceComplexHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstCompleteSpaceHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstZero

/-!
# QuantumMechanics.QuantumSystem.UnitaryRelation

Topic: quantum_mechanics   Node: 23703964e17f

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.QuantumSystem.UnitaryRelation`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/QuantumSystem/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation on quantum systems where `Q₁` is related to `Q₂` if there exists a linear isometry equivalence `e : Q₁.HS ≃ₗᵢ[ℂ] Q₂.HS` between the respective Hilbert spaces satisfying `e ∘ Q₁.ℋ ∘ e.symm = Q₂.ℋ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
/-- The relation on quantum systems where `Q₁` is related to `Q₂` if there exists a linear isometry equivalence `e : Q₁.HS ≃ₗᵢ[ℂ] Q₂.HS` between the respective Hilbert spaces satisfying `e ∘ Q₁.ℋ ∘ e.symm = Q₂.ℋ`. -/
noncomputable def QuantumMechanics.QuantumSystem.UnitaryRelation (Q₁ Q₂ : QuantumSystem) : Prop :=
  ∃ (e : Q₁.HS ≃ₗᵢ[ℂ] Q₂.HS) (h : Q₁.ℋ.domain.map e.toLinearMap = Q₂.ℋ.domain),
    ∀ ψ : Q₁.ℋ.domain, e (Q₁.ℋ ψ) = Q₂.ℋ ⟨e ψ, by simp [← h]⟩
