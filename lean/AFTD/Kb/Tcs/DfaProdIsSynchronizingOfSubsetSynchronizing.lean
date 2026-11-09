import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaIsSubsetSynchronizing
import AFTD.Kb.Tcs.DfaProdIsSynchronizingIff

/-!
# dfa_prod_is_synchronizing_of_subset_synchronizing

Topic: automata   Node: c9f13fa9fc1b

Provenance: formalization of a published result. Source: arXiv:2611.09136 Sec. 7

If `w₁` is a synchronizing word for `A₁`, and `v` is a subset-synchronizing word for the image set of `w₁` on `A₂`, then the concatenated word `w₁ ++ v` is a synchronizing word for the direct product `dfa_prod A₁ A₂`.
-/

/-- Concatenating a synchronizing word for A₁ with a word that subset-synchronizes its image in A₂ yields a synchronizing word for the direct product. -/
theorem dfa_prod_is_synchronizing_of_subset_synchronizing {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) (w₁ v : List α) (hw₁ : dfa_is_synchronizing A₁ w₁) (hv : dfa_is_subset_synchronizing A₂ (Set.range (fun q : σ₂ => A₂.evalFrom q w₁)) v) : dfa_is_synchronizing (dfa_prod A₁ A₂) (w₁ ++ v) := by
  intro ⟨q₁, q₂⟩ ⟨r₁, r₂⟩
  rw [dfa_prod_is_synchronizing_iff_evalFrom, dfa_prod_is_synchronizing_iff_evalFrom]
  ext
  · dsimp
    rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append, hw₁ q₁ r₁]
  · dsimp
    rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append]
    exact hv _ (Set.mem_range_self q₂) _ (Set.mem_range_self r₂)
