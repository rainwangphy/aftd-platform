import AFTD.Prelude

/-!
# three_hadamard_clean_return_phases

Topic: quantum   Node: 7dc3b617326d

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

For unit complex phases u and v, vanishing of the unwanted numerator 1-u+v+u*v of an alternating three-Hadamard chain forces u=v and v=i or v=-i.
-/

theorem three_hadamard_clean_return_phases (u v : ℂ)
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hreturn : 1 - u + v + u * v = 0) :
    u = v ∧ (v = Complex.I ∨ v = -Complex.I) := by
  have he : 1 + v = u * (1 - v) := by linear_combination hreturn
  have hn := congrArg Complex.normSq he
  rw [map_mul, hu, one_mul] at hn
  have hr : v.re = 0 := by
    simp only [Complex.normSq_add, Complex.normSq_sub, hv, map_one,
      Complex.conj_re, one_mul] at hn
    linarith
  have hi : v.im = 1 ∨ v.im = -1 := by
    rw [Complex.normSq_apply, hr] at hv
    have hmul : (v.im - 1) * (v.im + 1) = 0 := by nlinarith [hv]
    rcases mul_eq_zero.mp hmul with h | h
    · left; linarith
    · right; linarith
  have hvv : v = Complex.I ∨ v = -Complex.I := by
    rcases hi with hi | hi
    · left; apply Complex.ext <;> simp [hr, hi]
    · right; apply Complex.ext <;> simp [hr, hi]
  have huv : u = v := by
    have hsq : v * v = -1 := by
      rcases hvv with h | h <;> rw [h] <;> simp
    have hne : 1 - v ≠ 0 := by
      intro h
      have : v = 1 := by linear_combination -h
      rw [this] at hr
      norm_num at hr
    apply mul_right_cancel₀ hne
    calc
      u * (1 - v) = 1 + v := he.symm
      _ = v * (1 - v) := by linear_combination hsq
  exact ⟨huv, hvv⟩
