import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.DfaProd

/-!
# dfa_prod_is_synchronizing_iff

Topic: automata   Node: 1dcb5e182676

Provenance: formalization of a published result. Source: arXiv:2611.09136 Lemma 3.1

A word `w` is synchronizing for the direct product `dfa_prod A₁ A₂` of two deterministic finite automata if and only if `w` is synchronizing for both `A₁` and `A₂`.
-/

lemma dfa_prod_is_synchronizing_iff_evalFrom {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) (q₁ : σ₁) (q₂ : σ₂) (w : List α) :
    (dfa_prod A₁ A₂).evalFrom (q₁, q₂) w = (A₁.evalFrom q₁ w, A₂.evalFrom q₂ w) := by
  induction w generalizing q₁ q₂ with
  | nil => rfl
  | cons a w ih =>
    simp only [DFA.evalFrom, List.foldl_cons]
    exact ih (A₁.step q₁ a) (A₂.step q₂ a)

/-- A word synchronizes the direct product of two DFAs iff it synchronizes both DFAs. -/
theorem dfa_prod_is_synchronizing_iff {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) (w : List α) : dfa_is_synchronizing (dfa_prod A₁ A₂) w ↔ dfa_is_synchronizing A₁ w ∧ dfa_is_synchronizing A₂ w := by
  constructor
  · intro h
    constructor
    · intro q₁ q₂
      have hprod := h (q₁, A₂.start) (q₂, A₂.start)
      rw [dfa_prod_is_synchronizing_iff_evalFrom, dfa_prod_is_synchronizing_iff_evalFrom] at hprod
      exact congrArg Prod.fst hprod
    · intro q₁ q₂
      have hprod := h (A₁.start, q₁) (A₁.start, q₂)
      rw [dfa_prod_is_synchronizing_iff_evalFrom, dfa_prod_is_synchronizing_iff_evalFrom] at hprod
      exact congrArg Prod.snd hprod
  · rintro ⟨h₁, h₂⟩ ⟨q₁, q₂⟩ ⟨r₁, r₂⟩
    rw [dfa_prod_is_synchronizing_iff_evalFrom, dfa_prod_is_synchronizing_iff_evalFrom]
    exact Prod.ext (h₁ q₁ r₁) (h₂ q₂ r₂)
