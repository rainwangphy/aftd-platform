import AFTD.Prelude

/-!
# six_colors_three_fixed_pair_intersects_image

Topic: combinatorics   Node: e5a6b26ef7fc

Provenance: helper lemma. Finite obstruction to fixed-signature three-edge gluing for OP-874; compatibility criterion in arXiv:2610.41950, Section 2.

For an injective map of six colors that fixes colors 0, 1, and 2, every two-element color set intersects its image. Hence no three-port signature with three distinct boundary colors can be glued to an identically normalized signature merely by permuting colors while preserving those boundary colors.
-/

set_option maxHeartbeats 3000000

theorem six_colors_three_fixed_pair_intersects_image
    (f : Fin 6 → Fin 6) (hinj : Function.Injective f)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : f 2 = 2)
    (x y : Fin 6) (hxy : x ≠ y) :
    ∃ z : Fin 6, (z = x ∨ z = y) ∧ (z = f x ∨ z = f y) := by
  by_contra h
  have hxx : x ≠ f x := by intro h'; exact h ⟨x, Or.inl rfl, Or.inl h'⟩
  have hxy' : x ≠ f y := by intro h'; exact h ⟨x, Or.inl rfl, Or.inr h'⟩
  have hyx : y ≠ f x := by intro h'; exact h ⟨y, Or.inr rfl, Or.inl h'⟩
  have hyy : y ≠ f y := by intro h'; exact h ⟨y, Or.inr rfl, Or.inr h'⟩
  have hx0 : x ≠ 0 := by intro hx; apply hxx; simpa [hx] using hf0.symm
  have hx1 : x ≠ 1 := by intro hx; apply hxx; simpa [hx] using hf1.symm
  have hx2 : x ≠ 2 := by intro hx; apply hxx; simpa [hx] using hf2.symm
  have hy0 : y ≠ 0 := by intro hy; apply hyy; simpa [hy] using hf0.symm
  have hy1 : y ≠ 1 := by intro hy; apply hyy; simpa [hy] using hf1.symm
  have hy2 : y ≠ 2 := by intro hy; apply hyy; simpa [hy] using hf2.symm
  have hfx0 : f x ≠ 0 := by intro h'; apply hx0; apply hinj; simpa [hf0] using h'
  have hfx1 : f x ≠ 1 := by intro h'; apply hx1; apply hinj; simpa [hf1] using h'
  have hfx2 : f x ≠ 2 := by intro h'; apply hx2; apply hinj; simpa [hf2] using h'
  have hfy0 : f y ≠ 0 := by intro h'; apply hy0; apply hinj; simpa [hf0] using h'
  have hfy1 : f y ≠ 1 := by intro h'; apply hy1; apply hinj; simpa [hf1] using h'
  have hfy2 : f y ≠ 2 := by intro h'; apply hy2; apply hinj; simpa [hf2] using h'
  have hfxfy : f x ≠ f y := fun he => hxy (hinj he)
  have bx := x.isLt
  have by' := y.isLt
  have bfx := (f x).isLt
  have bfy := (f y).isLt
  omega
