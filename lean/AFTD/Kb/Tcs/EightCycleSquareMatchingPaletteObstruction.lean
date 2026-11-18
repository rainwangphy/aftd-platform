import AFTD.Prelude

/-!
# eight_cycle_square_matching_palette_obstruction

Topic: combinatorics   Node: cc34484c8075

Provenance: helper lemma. Two matching-chord obstruction to globally square-coloring the complementary cycles in the two-versus-four route to OP-874, arXiv:2610.41950.

On an eight-cycle colored with four colors so that positions at distance one or two have different colors, at least one of the unordered color pairs at positions 4–5 and 0–1, or at positions 3–4 and 7–0, is equal to its counterpart.
-/

theorem eight_cycle_square_matching_palette_obstruction
    (a b c d e f g h : Fin 4)
    (H : a ≠ b ∧
      a ≠ c ∧
      b ≠ c ∧
      b ≠ d ∧
      c ≠ d ∧
      c ≠ e ∧
      d ≠ e ∧
      d ≠ f ∧
      e ≠ f ∧
      e ≠ g ∧
      f ≠ g ∧
      f ≠ h ∧
      g ≠ h ∧
      g ≠ a ∧
      h ≠ a ∧
      h ≠ b ∧
      ¬ ((e = a ∧ f = b) ∨ (e = b ∧ f = a)) ∧
      ¬ ((d = h ∧ e = a) ∨ (d = a ∧ e = h))) : False := by
  rcases H with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  fin_cases a <;> simp_all <;> fin_cases b <;> simp_all <;>
    fin_cases c <;> simp_all <;> fin_cases d <;> simp_all <;>
    fin_cases e <;> simp_all <;> fin_cases f <;> simp_all <;>
    fin_cases g <;> simp_all <;> fin_cases h <;> simp_all
