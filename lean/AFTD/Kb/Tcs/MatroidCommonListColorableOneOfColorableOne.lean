import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonColorable
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_list_colorable_one_of_colorable_one

Topic: combinatorics   Node: 8bc711f1173b

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Question 3.2 (the case χ ≤ 2 is known; this is the trivial case χ = 1, which needs no strong base orderability)

If (M₁, M₂) has a common coloring with one color (the whole ground set is independent in both), then it is 1-list-colorable: χ_ℓ = χ when χ ≤ 1.
-/

theorem matroid_common_list_colorable_one_of_colorable_one {α : Type*} (M₁ M₂ : Matroid α)
    (h : matroid_common_colorable M₁ M₂ 1) : matroid_common_list_colorable M₁ M₂ 1 := by
  obtain ⟨c, hlt, hc⟩ := h
  have hE : {e | e ∈ M₁.E ∧ c e = 0} = M₁.E := by
    ext e; exact ⟨fun h => h.1, fun h => ⟨h, Nat.lt_one_iff.1 (hlt e h)⟩⟩
  have h1 : M₁.Indep M₁.E := hE ▸ (hc 0).1
  have h2 : M₂.Indep M₁.E := hE ▸ (hc 0).2
  classical
  intro L hL
  refine ⟨fun e => if he : e ∈ M₁.E then
      (Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one (hL e he))).choose else 0, ?_, ?_⟩
  · intro e he
    simp only [he, dite_true]
    exact (Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one (hL e he))).choose_spec
  · intro γ
    exact ⟨h1.subset fun e he => he.1, h2.subset fun e he => he.1⟩
