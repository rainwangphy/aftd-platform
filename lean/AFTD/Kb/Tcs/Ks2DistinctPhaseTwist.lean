import AFTD.Prelude
import AFTD.Kb.Tcs.Ks2InstanceVector
import AFTD.Kb.Tcs.Ks2InstanceOuter

/-!
# ks2_distinct_phase_twist

Topic: np_completeness   Node: 765312a16ffd

Provenance: original. Related work: OP-2182 (arXiv:2611.27740, Section 4). The paper's reduction uses repeated vectors and asks whether hardness survives without them; this shows that over C^d any family of nonzero vectors can be made pairwise distinct, within the Gaussian-rational encoding, without changing any outer product v v† (multiply the vectors by unit-modulus Gaussian rationals ((k^2-1) + 2k i)/(k^2+1)).

For every dimension d and every list vs of encoded vectors (entries (t, w) with t rational and w a list of pairs of rationals) all of whose vectors ks2_instance_vector d p, p in vs, are nonzero, there is a list vs' of encoded vectors such that the list of outer products ks2_instance_outer d p' for p' in vs' equals the list of outer products ks2_instance_outer d p for p in vs (same length, equal position by position), and the vectors ks2_instance_vector d p' for p' in vs' are pairwise distinct (the mapped list has no duplicates).
-/

def ks2_twist (k : ℕ) (p : ℚ × List (ℚ × ℚ)) : ℚ × List (ℚ × ℚ) :=
  (p.1, p.2.map (fun z =>
    (z.1 * (((k:ℚ)^2 - 1) / ((k:ℚ)^2 + 1)) - z.2 * (2 * k / ((k:ℚ)^2 + 1)),
     z.1 * (2 * k / ((k:ℚ)^2 + 1)) + z.2 * (((k:ℚ)^2 - 1) / ((k:ℚ)^2 + 1)))))

noncomputable def ks2_phase (k : ℕ) : ℂ :=
  ((((k:ℚ)^2 - 1) / ((k:ℚ)^2 + 1) : ℚ) : ℂ) + ((2 * k / ((k:ℚ)^2 + 1) : ℚ) : ℂ) * Complex.I

theorem ks2_twist_vector (d k : ℕ) (p : ℚ × List (ℚ × ℚ)) :
    ks2_instance_vector d (ks2_twist k p) = ks2_phase k • ks2_instance_vector d p := by
  funext j
  have h : ∀ (w : List (ℚ × ℚ)) (g : ℚ × ℚ → ℚ × ℚ), g (0, 0) = (0, 0) →
      (w.map g).getD j.val (0, 0) = g (w.getD j.val (0, 0)) := by
    intro w g hg
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[j.val]? <;> simp [hg]
  simp only [ks2_instance_vector, ks2_twist, ks2_phase, Pi.smul_apply, smul_eq_mul]
  rw [h _ _ (by simp)]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem ks2_phase_norm (k : ℕ) : ks2_phase k * star (ks2_phase k) = 1 := by
  have hk : ((k:ℂ)^2 + 1) ≠ 0 := by
    have : ((k:ℂ)^2 + 1) = (((k:ℝ)^2 + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by positivity : ((k:ℝ)^2 + 1) ≠ 0)
  simp only [ks2_phase]
  push_cast
  simp only [star_add, star_mul', Complex.star_def, Complex.conj_I, map_div₀, map_sub, map_add,
    map_pow, Complex.conj_natCast, map_one, map_mul, map_ofNat]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem ks2_phase_injective : Function.Injective ks2_phase := by
  have hre : ∀ k : ℕ, (ks2_phase k).re = ((k:ℝ)^2 - 1) / ((k:ℝ)^2 + 1) := by
    intro k
    have : ks2_phase k = ((((k:ℝ)^2 - 1) / ((k:ℝ)^2 + 1) : ℝ) : ℂ) +
        ((2 * k / ((k:ℝ)^2 + 1) : ℝ) : ℂ) * Complex.I := by
      simp [ks2_phase]
    rw [this]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_self, add_zero]
  intro k l h
  have h1 := congrArg Complex.re h
  rw [hre, hre] at h1
  have hk : (0:ℝ) < (k:ℝ)^2 + 1 := by positivity
  have hl : (0:ℝ) < (l:ℝ)^2 + 1 := by positivity
  rw [div_eq_div_iff hk.ne' hl.ne'] at h1
  have h2 : (k:ℝ)^2 = (l:ℝ)^2 := by nlinarith
  have h3 := (sq_eq_sq₀ (by positivity) (by positivity)).mp h2
  exact_mod_cast h3

theorem ks2_twist_outer (d k : ℕ) (p : ℚ × List (ℚ × ℚ)) :
    ks2_instance_outer d (ks2_twist k p) = ks2_instance_outer d p := by
  ext i j
  simp only [ks2_instance_outer, ks2_twist_vector, Matrix.vecMulVec_apply, Pi.smul_apply,
    Pi.star_apply, smul_eq_mul, star_mul']
  have := ks2_phase_norm k
  linear_combination (ks2_instance_vector d p i * star (ks2_instance_vector d p j)) * this

theorem ks2_distinct_phase_twist (d : ℕ) (vs : List (ℚ × List (ℚ × ℚ)))
    (hne : ∀ p ∈ vs, ks2_instance_vector d p ≠ 0) :
    ∃ vs' : List (ℚ × List (ℚ × ℚ)),
      vs'.map (ks2_instance_outer d) = vs.map (ks2_instance_outer d) ∧
      (vs'.map (ks2_instance_vector d)).Nodup := by
  classical
  induction vs with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons p vs ih =>
    obtain ⟨vs', h1, h2⟩ := ih (fun q hq => hne q (List.mem_cons_of_mem _ hq))
    have hp := hne p List.mem_cons_self
    have hinj : Function.Injective (fun k : ℕ => ks2_instance_vector d (ks2_twist k p)) := by
      intro k l h
      simp only [ks2_twist_vector] at h
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hp
      have := congrFun h j
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact ks2_phase_injective (mul_right_cancel₀ hj this)
    obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset
      ((vs'.map (ks2_instance_vector d)).toFinset.preimage _ hinj.injOn)
    refine ⟨ks2_twist k p :: vs', ?_, ?_⟩
    · simp [h1, ks2_twist_outer]
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, h2⟩
      simpa using hk
