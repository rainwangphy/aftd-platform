import AFTD.Prelude

/-!
# list_lex_map_iff_of_strictMono

Topic: fair_division   Node: 46d493ce3dda

A strictly monotone map from naturals to reals preserves and reflects the strict lexicographic order on lists.
-/

/-- Lexicographic order is preserved and reflected by a strictly monotone map. -/
lemma list_lex_map_iff_of_strictMono {f : ℕ → ℝ} (hf : StrictMono f) :
    ∀ l₁ l₂ : List ℕ, List.Lex (· < ·) (l₁.map f) (l₂.map f) ↔ List.Lex (· < ·) l₁ l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; cases l₂ <;> simp
  | cons a l₁ ih =>
    intro l₂
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      simp only [List.map_cons, List.cons_lex_cons_iff, hf.lt_iff_lt, hf.injective.eq_iff, ih l₂]
