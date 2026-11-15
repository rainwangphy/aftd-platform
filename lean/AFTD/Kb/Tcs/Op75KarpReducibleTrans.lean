import AFTD.Prelude
import AFTD.Kb.Tcs.KarpReducible
import AFTD.Kb.Tcs.Op75Tm2InhabitedComp
import AFTD.Kb.Tcs.Op75Tm2EmptyComp

/-!
# op75_karp_reducible_trans

Topic: np_completeness   Node: 58fd65156f72

Provenance: helper lemma. OP-75 complexity reduction; transitivity of polynomial-time many-one reductions for the repository TM2 model.

Polynomial-time many-one reducibility is transitive for languages over arbitrary alphabets under the repository TM2 definition.
-/

theorem op75_karp_reducible_trans (Γ₀ Γ₁ Γ₂ : Type) (L₀ : Language Γ₀) (L₁ : Language Γ₁) (L₂ : Language Γ₂) : KarpReducible Γ₀ Γ₁ L₀ L₁ → KarpReducible Γ₁ Γ₂ L₁ L₂ → KarpReducible Γ₀ Γ₂ L₀ L₂ := by
  classical
  rintro ⟨f, hf, h₁⟩ ⟨g, hg, h₂⟩
  refine ⟨g ∘ f, ?_, fun w => (h₁ w).trans (h₂ (f w))⟩
  by_cases h : Nonempty Γ₁
  · letI : Inhabited Γ₁ := ⟨Classical.choice h⟩
    exact op75_tm2_inhabited_comp hf hg
  · letI : IsEmpty Γ₁ := ⟨fun x => h ⟨x⟩⟩
    exact op75_tm2_empty_comp hf hg
