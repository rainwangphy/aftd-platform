import AFTD.Prelude

/-!
# ag_abs_aux

Topic: equilibria   Node: 226b9cb05bc2

Elementary inequality behind the Lipschitz bound.
-/

/-- Elementary inequality behind the Lipschitz bound. -/
theorem ag_abs_aux (a b d : ℚ) (hb : (0 ≤ b ∧ b ≤ d) ∨ (d ≤ b ∧ b ≤ 0)) :
    2 * |a + b| ≤ |a| + |d| + |a + d| := by
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases abs_cases (a + b) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases abs_cases a with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
    rcases abs_cases d with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
    rcases abs_cases (a + d) with ⟨e4, _⟩ | ⟨e4, _⟩ <;>
    linarith
