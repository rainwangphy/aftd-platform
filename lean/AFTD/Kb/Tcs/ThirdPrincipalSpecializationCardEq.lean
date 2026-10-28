import AFTD.Prelude
import AFTD.Kb.Tcs.ThirdPrincipalSpecialization
import AFTD.Kb.Tcs.ThirdPrincipalSpecializationEvalOne
import AFTD.Kb.Tcs.IsTreeCardColoringThree

/-!
# third_principal_specialization_card_eq

Topic: graphs   Node: bf7242ad1421

Provenance: formalization of a published result. Source: arXiv:2610.31785 Proposition 3.3

The third principal specialization of any finite tree on at least one vertex uniquely determines its number of vertices.
-/

/-- The third principal specialization of any tree determines its number of vertices. -/
theorem third_principal_specialization_card_eq {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] (T₁ : SimpleGraph V₁) (T₂ : SimpleGraph V₂) [DecidableRel T₁.Adj] [DecidableRel T₂.Adj] (hT₁ : T₁.IsTree) (hT₂ : T₂.IsTree) (heq : third_principal_specialization T₁ = third_principal_specialization T₂) : Fintype.card V₁ = Fintype.card V₂ := by
  have h₁ := third_principal_specialization_eval_one T₁
  have h₂ := third_principal_specialization_eval_one T₂
  rw [is_tree_card_coloring_three T₁ hT₁] at h₁
  rw [is_tree_card_coloring_three T₂ hT₂] at h₂
  have hpoly : MvPolynomial.eval (fun _ : Fin 2 => (1:ℤ)) (third_principal_specialization T₁)
      = MvPolynomial.eval (fun _ : Fin 2 => (1:ℤ)) (third_principal_specialization T₂) := by
    rw [heq]
  rw [h₁, h₂] at hpoly
  have hn : 3 * 2 ^ (Fintype.card V₁ - 1) = 3 * 2 ^ (Fintype.card V₂ - 1) := by
    exact_mod_cast hpoly
  have h2 : 2 ^ (Fintype.card V₁ - 1) = 2 ^ (Fintype.card V₂ - 1) :=
    Nat.mul_left_cancel (by norm_num) hn
  have hab : Fintype.card V₁ - 1 = Fintype.card V₂ - 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
  have n1 : 0 < Fintype.card V₁ := Fintype.card_pos_iff.mpr hT₁.connected.nonempty
  have n2 : 0 < Fintype.card V₂ := Fintype.card_pos_iff.mpr hT₂.connected.nonempty
  omega
