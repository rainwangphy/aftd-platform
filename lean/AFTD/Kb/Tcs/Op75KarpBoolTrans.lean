import AFTD.Prelude
import AFTD.Kb.Tcs.KarpReducible
import AFTD.Kb.Tcs.Op75Tm2OutputLinearBound
import AFTD.Kb.Tcs.Op75Tm2BoolComp

/-!
# op75_karp_bool_trans

Topic: np_completeness   Node: d394dabdd4a8

Provenance: helper lemma. OP-75 reduction composition with the canonical Boolean subset-sum source language.

Polynomial-time many-one reductions compose when their intermediate language uses the Boolean alphabet, even if the source and target alphabets are arbitrary.
-/

theorem op75_karp_bool_trans (Γ₀ Γ₂ : Type) (L₀ : Language Γ₀) (L₁ : Language Bool) (L₂ : Language Γ₂) : KarpReducible Γ₀ Bool L₀ L₁ → KarpReducible Bool Γ₂ L₁ L₂ → KarpReducible Γ₀ Γ₂ L₀ L₂ := by
  rintro ⟨f, hf, hL⟩ ⟨g, hg, hM⟩
  refine ⟨g ∘ f, op75_tm2_bool_comp hf hg, ?_⟩
  intro w
  exact (hL w).trans (hM (f w))
