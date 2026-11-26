import AFTD.Prelude

/-!
# op874_cycle_palette_kernel

Topic: graphs   Node: bbd701ab3fe1

Provenance: helper lemma. Four-color arithmetic for the OP-874 local interface analysis, https://arxiv.org/abs/2610.41950.

For four colors, the listed properness and adjacent-palette inequalities on an eight-edge cyclic word, together with two matching-palette distinctions, force a repetition between two consecutive colors among positions 1, 3, 5, and 7.
-/

private theorem op874_no_five_distinct_high_colors (a b c d e : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : False := by
  have hs : ({a,b,c,d,e} : Finset (Fin 4)).card = 5 := by
    simp [hab,hac,had,hae,hbc,hbd,hbe,hcd,hce,hde]
  have hb := Finset.card_le_univ ({a,b,c,d,e} : Finset (Fin 4))
  simp only [Fintype.card_fin] at hb
  omega

theorem op874_cycle_palette_kernel
    (a x c t d y b s : Fin 4)
    (h₁ : a ≠ s) (h₂ : a ≠ x) (h₃ : c ≠ x) (h₄ : c ≠ t)
    (h₅ : d ≠ t) (h₆ : d ≠ y) (h₇ : b ≠ y) (h₈ : b ≠ s)
    (h₉ : a ≠ b) (h₁₀ : c ≠ d) (h₁₁ : a ≠ c) (h₁₂ : d ≠ b)
    (hp : ¬ ((s = t ∧ a = d) ∨ (s = d ∧ a = t)))
    (hq : ¬ ((s = t ∧ b = c) ∨ (s = c ∧ b = t))) :
    x = t ∨ t = y ∨ y = s ∨ s = x := by
  by_contra hn
  push Not at hn
  have hA : s = c ∨ t = a ∨ s = t := by
    by_contra h
    push Not at h
    exact op874_no_five_distinct_high_colors a c s t x h₁₁ h₁ h.2.1.symm h₂ h.1.symm h₄ h₃ h.2.2 hn.2.2.2 hn.1.symm
  have hB : s = d ∨ t = b ∨ s = t := by
    by_contra h
    push Not at h
    exact op874_no_five_distinct_high_colors b d s t y h₁₂.symm h₈ h.2.1.symm h₇ h.1.symm h₅ h₆ h.2.2 hn.2.2.1.symm hn.2.1
  have hst : s ≠ t := by
    intro he
    have had : a ≠ d := by intro h; exact hp (Or.inl ⟨he,h⟩)
    have hbc : b ≠ c := by intro h; exact hq (Or.inl ⟨he,h⟩)
    have hcs : c ≠ s := by simpa [he] using h₄
    have hds : d ≠ s := by simpa [he] using h₅
    exact op874_no_five_distinct_high_colors a b c d s h₉ h₁₁ had h₁ hbc h₁₂.symm h₈ h₁₀ hcs hds
  rcases hA with hsc | hta | he
  · rcases hB with hsd | htb | he
    · exact h₁₀ (hsc.symm.trans hsd)
    · exact hq (Or.inr ⟨hsc,htb.symm⟩)
    · exact hst he
  · rcases hB with hsd | htb | he
    · exact hp (Or.inr ⟨hsd,hta.symm⟩)
    · exact h₉ (hta.symm.trans htb)
    · exact hst he
  · exact hst he
