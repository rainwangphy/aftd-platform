import AFTD.Prelude
import AFTD.Kb.Tcs.PairEncode

/-!
# pair_encode_injective

Topic: complexity_basics   Node: ed2b99972af6

The pair encoding is injective: if pairEncode w₁ c₁ = pairEncode w₂ c₂ then w₁ = w₂ and c₁ = c₂.
-/

theorem pair_encode_injective_aux {Γ : Type} :
    ∀ (w₁ w₂ : List Γ) (x y : List (Γ ⊕ Unit)),
      List.map Sum.inl w₁ ++ Sum.inr () :: x = List.map Sum.inl w₂ ++ Sum.inr () :: y →
      w₁ = w₂ ∧ x = y := by
  intro w₁
  induction w₁ with
  | nil =>
    intro w₂ x y h
    cases w₂ with
    | nil => exact ⟨rfl, (List.cons.inj h).2⟩
    | cons b w₂ =>
      simp only [List.map_cons, List.map_nil, List.nil_append] at h
      exact absurd (List.cons.inj h).1 Sum.inr_ne_inl
  | cons a w₁ ih =>
    intro w₂ x y h
    cases w₂ with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.nil_append] at h
      exact absurd (List.cons.inj h).1 Sum.inl_ne_inr
    | cons b w₂ =>
      simp only [List.map_cons] at h
      obtain ⟨hab, htail⟩ := List.cons.inj h
      have hab' : a = b := Sum.inl_injective hab
      obtain ⟨hw, hxy⟩ := ih w₂ x y htail
      exact ⟨by rw [hab', hw], hxy⟩

/-- The pair encoding (w, c) ↦ w ++ [sep] ++ c is injective. -/
theorem pair_encode_injective {Γ : Type} {w₁ c₁ w₂ c₂ : List Γ}
    (h : pairEncode w₁ c₁ = pairEncode w₂ c₂) : w₁ = w₂ ∧ c₁ = c₂ := by
  simp only [pairEncode, List.singleton_append, List.append_assoc] at h
  obtain ⟨hw, hc⟩ :=
    pair_encode_injective_aux w₁ w₂ (List.map Sum.inl c₁) (List.map Sum.inl c₂) h
  exact ⟨hw, (Function.Injective.list_map Sum.inl_injective) hc⟩
