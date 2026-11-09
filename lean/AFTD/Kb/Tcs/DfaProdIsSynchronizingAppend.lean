import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaProdIsSynchronizingIff

/-!
# dfa_prod_is_synchronizing_append

Topic: automata   Node: 5baa737bb69f

Provenance: formalization of a published result. Source: arXiv:2611.09136 Lemma 3.3

If `w₁` is a synchronizing word for `A₁` and `w₂` is a synchronizing word for `A₂`, then the concatenated word `w₁ ++ w₂` is a synchronizing word for the direct product `dfa_prod A₁ A₂`.
-/

/-- Concatenation of synchronizing words for two DFAs synchronizes their direct product. -/
theorem dfa_prod_is_synchronizing_append {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) (w₁ w₂ : List α) (hw₁ : dfa_is_synchronizing A₁ w₁) (hw₂ : dfa_is_synchronizing A₂ w₂) : dfa_is_synchronizing (dfa_prod A₁ A₂) (w₁ ++ w₂) := by
  intro ⟨q₁, q₂⟩ ⟨r₁, r₂⟩
  rw [dfa_prod_is_synchronizing_iff_evalFrom, dfa_prod_is_synchronizing_iff_evalFrom]
  ext
  · dsimp
    rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append, hw₁ q₁ r₁]
  · dsimp
    rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append, hw₂ (A₂.evalFrom q₂ w₁) (A₂.evalFrom r₂ w₁)]
