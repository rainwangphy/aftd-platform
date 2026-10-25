import AFTD.Prelude

/-!
# four_hadamard_clean_return_phases

Topic: quantum   Node: ed47b7f17328

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

For unit complex u,v,w, the clean-return equation (1+u)*(1-w)+v*(1-u)*(1+w)=0 implies one of: u=w=1; u=w=-1; v=1 and u*w=1; or v=-1 and u=w.
-/

theorem four_hadamard_clean_return_phases (u v w : ℂ)
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w = 1)
    (hreturn : (1 + u) * (1 - w) + v * (1 - u) * (1 + w) = 0) :
    (u = 1 ∧ w = 1) ∨ (u = -1 ∧ w = -1) ∨
      (v = 1 ∧ u * w = 1) ∨ (v = -1 ∧ u = w) := by
  have he : (1 + u) * (1 - w) = -v * ((1 - u) * (1 + w)) := by
    linear_combination hreturn
  have hn := congrArg Complex.normSq he
  simp only [map_mul, Complex.normSq_add, Complex.normSq_sub,
    hu, hw, map_one, Complex.conj_re, one_mul] at hn
  rw [Complex.normSq_neg, hv] at hn
  have hre : u.re = w.re := by nlinarith [hn]
  have him : u.im = w.im ∨ u.im = -w.im := by
    simp only [Complex.normSq_apply] at hu hw
    rw [hre] at hu
    have : (u.im - w.im) * (u.im + w.im) = 0 := by nlinarith [hu, hw]
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  have hwcase : w = u ∨ w = star u := by
    rcases him with h | h
    · left; apply Complex.ext <;> simp_all
    · right; apply Complex.ext <;> simp_all
  rcases hwcase with hwu | hwu
  · subst w
    have hf : (1 - u) * (1 + u) * (1 + v) = 0 := by
      linear_combination hreturn
    rcases mul_eq_zero.mp hf with h | h
    · rcases mul_eq_zero.mp h with h | h
      · have : u = 1 := by linear_combination -h
        exact Or.inl ⟨this, this⟩
      · have : u = -1 := by linear_combination h
        exact Or.inr (Or.inl ⟨this, this⟩)
    · have : v = -1 := by linear_combination h
      exact Or.inr (Or.inr (Or.inr ⟨this, rfl⟩))
  · subst w
    have hc : u * star u = 1 := by simpa [Complex.mul_conj] using hu
    have hf : (1 - u) * (1 + u) * (1 - v) = 0 := by
      linear_combination -u * hreturn - (1 + u - v + u*v) * hc
    rcases mul_eq_zero.mp hf with h | h
    · rcases mul_eq_zero.mp h with h | h
      · have hh : u = 1 := by linear_combination -h
        exact Or.inl ⟨hh, by simp [hh]⟩
      · have hh : u = -1 := by linear_combination h
        exact Or.inr (Or.inl ⟨hh, by simp [hh]⟩)
    · have hh : v = 1 := by linear_combination -h
      exact Or.inr (Or.inr (Or.inl ⟨hh, hc⟩))
