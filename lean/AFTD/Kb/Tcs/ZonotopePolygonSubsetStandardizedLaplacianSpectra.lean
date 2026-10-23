import AFTD.Prelude
import AFTD.Kb.Tcs.StandardizedLaplacianSpectra
import AFTD.Kb.Tcs.IsStandardizedLaplacian
import AFTD.Kb.Tcs.CirculantLaplacianIsStandardized

/-!
# zonotope_polygon_subset_standardized_laplacian_spectra

Topic: graphs   Node: 6591f8e4d8d3

Provenance: formalization of a published result. Source: arXiv:2610.14100 Corollary 2

For any integer n ≥ 2, the zonotope polygon S_n, defined as the set of linear combinations ∑_{m=1}^{n-1} t_m g_m with t_m ∈ [0, 1] and g_m = (1/n)(1 - exp(-2πi m/n)), is a subset of the standardized Laplacian spectrum Lambda_n.
-/

/-- The zonotope polygon S_n is contained in the standardized Laplacian spectrum Lambda_n (PR-360). -/
theorem zonotope_polygon_subset_standardized_laplacian_spectra (n : ℕ) (hn : 2 ≤ n) :
    { z : ℂ | ∃ t : ℕ → ℝ, (∀ m ∈ Finset.Ico 1 n, 0 ≤ t m ∧ t m ≤ 1) ∧
      z = ∑ m ∈ Finset.Ico 1 n, (t m : ℂ) * ((1 / (n : ℂ)) * (1 - Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) / (n : ℂ)))) } ⊆
    standardized_laplacian_spectra n := by
  rintro z ⟨t, ht, hz⟩
  rw [hz]
  set Z : ℂ := ∑ m ∈ Finset.Ico 1 n, (t m : ℂ) * ((1 / (n : ℂ)) * (1 - Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) / (n : ℂ)))) with hZdef
  have hnpos : 0 < n := by omega
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hnpos)
  set μ : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) / (n : ℂ)) with hμdef
  set L : Matrix (Fin n) (Fin n) ℝ := (1 / (n : ℝ)) • ∑ m ∈ Finset.Ico 1 n, t m • ((1 : Matrix (Fin n) (Fin n) ℝ) - Matrix.of (fun i j : Fin n => if (j : ℕ) = ((i : ℕ) + m) % n then (1:ℝ) else 0)) with hL
  set A : Matrix (Fin n) (Fin n) ℂ := (1 / (n : ℂ)) • ∑ m ∈ Finset.Ico 1 n, (t m : ℂ) • ((1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.of (fun i j : Fin n => if (j : ℕ) = ((i : ℕ) + m) % n then (1:ℂ) else 0)) with hA
  refine ⟨L, circulant_laplacian_is_standardized n hn t ht, ?_⟩
  have hmap : L.map Complex.ofReal = A := by
    rw [hL, hA]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.of_apply, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_one, Complex.ofReal_zero,
      Complex.ofReal_sub, apply_ite Complex.ofReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show ((1 / (n:ℝ) : ℝ) : ℂ) = 1 / (n:ℂ) from by push_cast; ring]
  rw [hmap]
  rw [spectrum.mem_iff]
  intro hunit
  have hμn : μ ^ n = 1 := by
    rw [hμdef, ← Complex.exp_nat_mul]
    have harg : (n : ℂ) * (-(2 * Real.pi * Complex.I) / (n : ℂ)) = (-1 : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  have hμmod : ∀ k : ℕ, μ ^ (k % n) = μ ^ k := by
    intro k
    conv_rhs => rw [← Nat.mod_add_div k n]
    rw [pow_add, pow_mul, hμn, one_pow, mul_one]
  have hbase : ∀ m : ℕ, Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) / (n : ℂ)) = μ ^ m := by
    intro m
    rw [hμdef, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  set v : Fin n → ℂ := fun i => μ ^ (i : ℕ) with hv
  have hvne : v ≠ 0 := by
    intro h
    have h0 := congrFun h ⟨0, hnpos⟩
    simp [hv] at h0
  have hM : ∀ m, (Matrix.of (fun i j : Fin n => if (j:ℕ) = ((i:ℕ)+m)%n then (1:ℂ) else 0)).mulVec v = μ^m • v := by
    intro m
    ext i
    simp only [hv, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (⟨((i:ℕ)+m)%n, Nat.mod_lt _ hnpos⟩ : Fin n)]
    · simp only [if_true, one_mul]
      rw [hμmod, pow_add]
      ring
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hAv : A.mulVec v = Z • v := by
    rw [hZdef, hA]
    rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
    have hper : ∀ m, ((t m : ℂ) • ((1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.of (fun i j : Fin n => if (j:ℕ) = ((i:ℕ)+m)%n then (1:ℂ) else 0))).mulVec v
        = ((t m : ℂ) * (1 - μ^m)) • v := by
      intro m
      rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hM m]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun m _ => hper m)]
    rw [← Finset.sum_smul]
    rw [smul_smul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [hbase m]
    ring
  rw [Algebra.algebraMap_eq_smul_one] at hunit
  have hinj := Matrix.mulVec_injective_of_isUnit hunit
  have hz1 : (Z • (1 : Matrix (Fin n) (Fin n) ℂ) - A).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv]
    simp
  have h0 : (Z • (1 : Matrix (Fin n) (Fin n) ℂ) - A).mulVec v = (Z • (1 : Matrix (Fin n) (Fin n) ℂ) - A).mulVec 0 := by
    rw [Matrix.mulVec_zero]
    exact hz1
  exact hvne (hinj h0)
