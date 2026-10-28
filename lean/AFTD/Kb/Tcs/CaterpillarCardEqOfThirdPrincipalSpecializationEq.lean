import AFTD.Prelude
import AFTD.Kb.Tcs.IsCaterpillarIsTree
import AFTD.Kb.Tcs.ThirdPrincipalSpecializationCardEq
import AFTD.Kb.Tcs.ThirdPrincipalSpecialization
import AFTD.Kb.Tcs.IsCaterpillar

/-!
# caterpillar_card_eq_of_third_principal_specialization_eq

Topic: graphs   Node: 12eb3970d871

Provenance: helper lemma. step towards caterpillar_third_t_chromatic_specialization_fiber_le_two

If two finite caterpillars have equal third principal specializations, their vertex sets have equal cardinalities.
-/

/-- Two finite caterpillars with equal third principal specializations have equal vertex counts. -/
theorem caterpillar_card_eq_of_third_principal_specialization_eq
    {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]
    (T₁ : SimpleGraph V₁) (T₂ : SimpleGraph V₂)
    [DecidableRel T₁.Adj] [DecidableRel T₂.Adj]
    (hT₁ : is_caterpillar T₁) (hT₂ : is_caterpillar T₂)
    (heq : third_principal_specialization T₁ = third_principal_specialization T₂) :
    Fintype.card V₁ = Fintype.card V₂ := by
  exact third_principal_specialization_card_eq T₁ T₂ (is_caterpillar_isTree T₁ hT₁) (is_caterpillar_isTree T₂ hT₂) heq
