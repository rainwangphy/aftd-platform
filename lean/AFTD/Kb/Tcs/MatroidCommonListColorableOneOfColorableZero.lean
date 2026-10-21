import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonColorable
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_list_colorable_one_of_colorable_zero

Topic: combinatorics   Node: d67a3e28c111

Provenance: helper lemma. step towards matroid_common_list_colorable_succ_of_common_colorable

If two matroids have a common coloring with 0 colors, then their ground set is empty, so they are 1-list-colorable.
-/

/-- Base case k = 0 of one-step list-lifting: if two loopless matroids on a common ground set have a common coloring with 0 colors, then the ground set is empty and they are 1-list-colorable. -/
theorem matroid_common_list_colorable_one_of_colorable_zero {α : Type*} (M₁ M₂ : Matroid α)
    (h : matroid_common_colorable M₁ M₂ 0) :
    matroid_common_list_colorable M₁ M₂ 1 := by
  obtain ⟨c₀, hlt, -⟩ := h
  have hE : M₁.E = ∅ := Set.eq_empty_iff_forall_notMem.2 fun e he => Nat.not_lt_zero _ (hlt e he)
  intro L _
  refine ⟨fun _ => 0, fun e he => (Set.eq_empty_iff_forall_notMem.1 hE e he).elim, fun γ => ?_⟩
  have h_empty : {e : α | e ∈ M₁.E ∧ (fun _ : α => (0 : ℕ)) e = γ} = ∅ := by
    ext e
    simp [hE]
  rw [h_empty]
  exact ⟨M₁.empty_indep, M₂.empty_indep⟩
