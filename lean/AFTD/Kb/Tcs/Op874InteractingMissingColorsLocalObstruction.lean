import AFTD.Prelude
import AFTD.Kb.Tcs.Op874TwoColorCoreAdj

/-!
# op874_interacting_missing_colors_local_obstruction

Topic: graphs   Node: 74e7205da9a0

Provenance: helper lemma. Local-state counting obstruction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

Two missing-color triangles with leaves and a cross edge force incompatible opposite-port selections, even though each single-color constraint graph is a pseudoforest.
-/

theorem op874_interacting_missing_colors_local_obstruction
    (h : Fin 10 → Fin 10 → Fin 6)
    (hi : ∀ v x y, op874_two_color_core_adj v x → op874_two_color_core_adj v y →
      x ≠ y → h v x ≠ h v y)
    (a₁ : h 0 6 = 1 ∨ h 6 0 = 1)
    (a₂ : h 0 9 = 1 ∨ h 9 0 = 1)
    (a₃ : h 6 9 = 1 ∨ h 9 6 = 1)
    (a₄ : h 7 9 = 1 ∨ h 9 7 = 1)
    (a₅ : h 7 9 = 2 ∨ h 9 7 = 2)
    (a₆ : h 6 9 = 2 ∨ h 9 6 = 2)
    (b₁ : h 2 4 = 4 ∨ h 4 2 = 4)
    (b₂ : h 2 8 = 4 ∨ h 8 2 = 4)
    (b₃ : h 4 8 = 4 ∨ h 8 4 = 4)
    (b₄ : h 5 8 = 4 ∨ h 8 5 = 4)
    (b₅ : h 5 8 = 2 ∨ h 8 5 = 2)
    (b₆ : h 4 8 = 2 ∨ h 8 4 = 2)
    (cross : h 4 6 = 2 ∨ h 6 4 = 2) : False := by
  have d₀ := hi 0 6 9 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₂ := hi 2 4 8 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₄a := hi 4 2 6 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₄b := hi 4 2 8 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₄c := hi 4 6 8 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₆a := hi 6 0 4 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₆b := hi 6 0 9 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₆c := hi 6 4 9 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₈a := hi 8 2 4 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₈b := hi 8 2 5 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₈c := hi 8 4 5 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₉a := hi 9 0 6 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₉b := hi 9 0 7 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have d₉c := hi 9 6 7 (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj]) (by simp [op874_two_color_core_adj])
  have leaf₁ : h 7 9 = 1 := by
    rcases a₄ with h | h
    · exact h
    · rcases a₁ with a₁ | a₁ <;> rcases a₂ with a₂ | a₂ <;>
        rcases a₃ with a₃ | a₃ <;> simp_all
  have leaf₄ : h 5 8 = 4 := by
    rcases b₄ with h | h
    · exact h
    · rcases b₁ with b₁ | b₁ <;> rcases b₂ with b₂ | b₂ <;>
        rcases b₃ with b₃ | b₃ <;> simp_all
  have q₉ : h 9 7 = 2 := by
    rcases a₅ with q | q
    · have : (1 : Fin 6) = 2 := leaf₁.symm.trans q
      contradiction
    · exact q
  have q₈ : h 8 5 = 2 := by
    rcases b₅ with q | q
    · have : (4 : Fin 6) = 2 := leaf₄.symm.trans q
      contradiction
    · exact q
  have q₆ : h 6 9 = 2 := by
    rcases a₆ with q | q
    · exact q
    · exact False.elim (d₉c (q.trans q₉.symm))
  have q₄ : h 4 8 = 2 := by
    rcases b₆ with q | q
    · exact q
    · exact False.elim (d₈c (q.trans q₈.symm))
  rcases cross with q | q
  · exact d₄c (q.trans q₄.symm)
  · exact d₆c (q.trans q₆.symm)
