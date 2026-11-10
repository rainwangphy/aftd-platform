import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.Weight
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# hilton_strong_incomparability_matrix

Topic: combinatorics   Node: 3dee311fe14d

Provenance: formalization of a published result. Source: arXiv:2611.12199, Theorem 2.1 (rank at most 2^(n-1) stated as a factorization L*R)

For every natural number n there are a field K, a matrix L over K with rows indexed by the subsets of Fin n and 2^(n-1) columns, and a matrix R over K with 2^(n-1) rows and columns indexed by the subsets of Fin n, such that the product M = L*R satisfies: M(A, B) = 0 whenever A and B are incomparable subsets (neither contains the other), and for every uncomplemented family F of subsets of Fin n (no set together with its complement), the principal submatrix of M on F has nonzero determinant.
-/

/-- zeta matrix of the Boolean lattice -/
noncomputable def hiltonZeta (R : Type) [CommRing R] (n : ℕ) : Matrix (Finset (Fin n)) (Finset (Fin n)) R :=
  Matrix.of fun A B => if A ⊆ B then 1 else 0

/-- Möbius matrix of the Boolean lattice -/
noncomputable def hiltonMobius (R : Type) [CommRing R] (n : ℕ) : Matrix (Finset (Fin n)) (Finset (Fin n)) R :=
  Matrix.of fun A B => if A ⊆ B then (-1 : R) ^ (B \ A).card else 0

/-- complementation matrix -/
noncomputable def hiltonCompl (R : Type) [CommRing R] (n : ℕ) : Matrix (Finset (Fin n)) (Finset (Fin n)) R :=
  Matrix.of fun A B => if A = Bᶜ then 1 else 0

theorem hilton_alt_sum_zero {R : Type} [CommRing R] {n : ℕ} (A B : Finset (Fin n)) (h : ¬ B ⊆ A) :
    ∑ C : Finset (Fin n), (if A ⊆ C then (-1 : R) ^ (C \ A).card else 0) *
      (if Cᶜ ⊆ B then 1 else 0) = 0 := by
  obtain ⟨i, hiB, hiA⟩ := Finset.not_subset.mp h
  set f : Finset (Fin n) → R := fun C => (if A ⊆ C then (-1 : R) ^ (C \ A).card else 0) *
      (if Cᶜ ⊆ B then 1 else 0) with hf
  have key : ∀ C, i ∉ C → f (insert i C) = - f C := by
    intro C hiC
    simp only [hf]
    have h1 : A ⊆ insert i C ↔ A ⊆ C := Finset.subset_insert_iff_of_notMem hiA
    have h2 : (insert i C)ᶜ ⊆ B ↔ Cᶜ ⊆ B := by
      rw [Finset.compl_insert]
      constructor
      · intro hiltonS x hx
        by_cases hxi : x = i
        · exact hxi ▸ hiB
        · exact hiltonS (Finset.mem_erase.mpr ⟨hxi, hx⟩)
      · intro hiltonS
        exact (Finset.erase_subset _ _).trans hiltonS
    have h3 : (insert i C \ A).card = (C \ A).card + 1 := by
      rw [Finset.insert_sdiff_of_notMem _ hiA, Finset.card_insert_of_notMem (by simp [hiC])]
    rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl, h3]
    split_ifs <;> simp [pow_succ]
  refine Finset.sum_involution (fun C _ => if i ∈ C then C.erase i else insert i C) ?_ ?_
    (fun _ _ => Finset.mem_univ _) ?_
  · intro C _
    show f C + f (if i ∈ C then C.erase i else insert i C) = 0
    by_cases hiC : i ∈ C
    · simp only [hiC, if_true]
      have := key (C.erase i) (Finset.notMem_erase i C)
      rw [Finset.insert_erase hiC] at this
      rw [this]
      ring
    · simp only [hiC, if_false]
      rw [key C hiC]
      ring
  · intro C _ _
    by_cases hiC : i ∈ C
    · simp [hiC, Finset.erase_eq_self]
    · simp [hiC, Finset.insert_eq_self]
  · intro C _
    by_cases hiC : i ∈ C
    · simp [hiC, Finset.insert_erase hiC]
    · simp [hiC, Finset.erase_insert hiC]

/-- the matrix `Zi * (diag q + s P) * Z` vanishes on incomparable pairs -/
theorem hilton_mat_zero_of_incomparable {R : Type} [CommRing R] {n : ℕ} (q : Finset (Fin n) → R) (s : R)
    (A B : Finset (Fin n)) (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A) :
    (hiltonMobius R n * (Matrix.diagonal q + s • hiltonCompl R n) * hiltonZeta R n) A B = 0 := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply]
  have e1 : (hiltonMobius R n * Matrix.diagonal q * hiltonZeta R n) A B = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun C _ => ?_)
    rw [Matrix.mul_diagonal]
    simp only [hiltonMobius, hiltonZeta, Matrix.of_apply]
    by_cases h1 : A ⊆ C
    · by_cases h2 : C ⊆ B
      · exact absurd (h1.trans h2) hAB
      · simp [h2]
    · simp [h1]
  have e2 : (hiltonMobius R n * hiltonCompl R n * hiltonZeta R n) A B = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have hPZ : ∀ C, (hiltonCompl R n * hiltonZeta R n) C B = if Cᶜ ⊆ B then 1 else 0 := by
      intro C
      rw [Matrix.mul_apply]
      simp only [hiltonCompl, hiltonZeta, Matrix.of_apply]
      rw [Finset.sum_eq_single Cᶜ]
      · simp
      · intro D _ hD
        have : C ≠ Dᶜ := by
          intro hC
          exact hD (by rw [hC, compl_compl])
        simp [this]
      · simp
    simp only [hPZ]
    simp only [hiltonMobius, Matrix.of_apply]
    exact hilton_alt_sum_zero A B hBA
  rw [e1, e2]
  simp

/-- a matrix on an `F`-indexed set, supported on `⊆` with unit diagonal, has determinant one -/
theorem hilton_det_unitri {K : Type} [CommRing K] {n : ℕ} (F : Finset (Finset (Fin n)))
    (W : Matrix F F K) (hW0 : ∀ a b : F, ¬ (a : Finset (Fin n)) ⊆ b → W a b = 0)
    (hW1 : ∀ a, W a a = 1) : W.det = 1 := by
  classical
  have hbt : W.BlockTriangular (fun a : F => (a : Finset (Fin n)).card) := by
    intro i j hij
    apply hW0
    intro hsub
    exact absurd (Finset.card_le_card hsub) (not_le.mpr hij)
  rw [hbt.det]
  refine Finset.prod_eq_one (fun k _ => ?_)
  have : W.toSquareBlock (fun a : F => (a : Finset (Fin n)).card) k = 1 := by
    ext ⟨a, ha⟩ ⟨c, hc⟩
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    by_cases hac : a = c
    · subst hac
      simp [hW1]
    · have hne : (⟨a, ha⟩ : {x : F // (x : Finset (Fin n)).card = k}) ≠ ⟨c, hc⟩ := fun h => hac (congrArg Subtype.val h)
      rw [if_neg hne]
      apply hW0
      intro hsub
      apply hac
      apply Subtype.ext
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [this, Matrix.det_one]


/-- the product of the variables outside the orbit of `A` -/
noncomputable def hiltonPi (n : ℕ) (A : Finset (Fin n)) : MvPolynomial (Finset (Fin n)) ℚ :=
  ∏ C ∈ (Finset.univ.erase A).erase Aᶜ, MvPolynomial.X C

/-- the product of all variables -/
noncomputable def hiltonS (n : ℕ) : MvPolynomial (Finset (Fin n)) ℚ := ∏ C, MvPolynomial.X C

/-- diagonal weight `q_A = x_A^2 Π'_A` -/
noncomputable def hiltonQ (n : ℕ) (A : Finset (Fin n)) : MvPolynomial (Finset (Fin n)) ℚ :=
  MvPolynomial.X A ^ 2 * hiltonPi n A

/-- the matrix `M = Z^{-1} (diag q + s P) Z` -/
noncomputable def hiltonMat (n : ℕ) : Matrix (Finset (Fin n)) (Finset (Fin n)) (MvPolynomial (Finset (Fin n)) ℚ) :=
  hiltonMobius _ n * (Matrix.diagonal (hiltonQ n) + hiltonS n • hiltonCompl _ n) * hiltonZeta _ n

theorem hilton_zeta_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    f.mapMatrix (hiltonZeta R n) = hiltonZeta S n := by
  ext A B
  simp [hiltonZeta, RingHom.mapMatrix_apply, apply_ite f]

theorem hilton_mobius_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    f.mapMatrix (hiltonMobius R n) = hiltonMobius S n := by
  ext A B
  simp [hiltonMobius, RingHom.mapMatrix_apply, apply_ite f]

theorem hilton_mat_det_ne {n : ℕ} (F : Finset (Finset (Fin n))) (hF : is_uncomplemented F) :
    ((hiltonMat n).submatrix (fun x : F => (x : Finset (Fin n)))
      (fun x : F => (x : Finset (Fin n)))).det ≠ 0 := by
  classical
  by_cases hF0 : F = ∅
  · haveI : IsEmpty F := Finset.isEmpty_coe_sort.mpr hF0
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  set m := F.card with hmdef
  have hm : 1 ≤ m := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hF0)
  set g : Finset (Fin n) → Polynomial ℚ := fun C => if Cᶜ ∈ F then Polynomial.X else 1 with hg
  set φ : MvPolynomial (Finset (Fin n)) ℚ →+* Polynomial ℚ := MvPolynomial.eval₂Hom Polynomial.C g
    with hφ
  set S := Finset.univ.filter (fun D : Finset (Fin n) => Dᶜ ∈ F) with hS
  have hcnt : S.card = m := by
    have : S = F.image compl := by
      ext D
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        exact ⟨Dᶜ, h, compl_compl D⟩
      · rintro ⟨a, ha, rfl⟩
        simpa using ha
    rw [this, Finset.card_image_of_injective _ compl_injective]
  have hprod : ∀ T : Finset (Finset (Fin n)),
      φ (∏ C ∈ T, MvPolynomial.X C) = Polynomial.X ^ (T.filter (fun D => Dᶜ ∈ F)).card := by
    intro T
    rw [map_prod]
    simp only [hφ, MvPolynomial.eval₂Hom_X', hg]
    rw [Finset.prod_ite]
    simp [Finset.prod_const]
  have hPi_card : ∀ A, ((Finset.univ.erase A).erase Aᶜ).filter (fun D => Dᶜ ∈ F) =
      (S.erase A).erase Aᶜ := by
    intro A
    rw [Finset.filter_erase, Finset.filter_erase]
  have hs_im : φ (hiltonS n) = Polynomial.X ^ m := by
    rw [hiltonS, hprod, ← hS, hcnt]
  have hqF : ∀ A ∈ F, φ (hiltonQ n A) = Polynomial.X ^ (m - 1) := by
    intro A hA
    have hAc : Aᶜ ∉ F := hF A hA
    have hAS : A ∉ S := by simpa [hS] using hAc
    have hAcS : Aᶜ ∈ S := by simpa [hS] using hA
    rw [hiltonQ, map_mul, map_pow, hiltonPi, hprod, hPi_card, Finset.erase_eq_of_notMem hAS,
      Finset.card_erase_of_mem hAcS, hcnt]
    simp [hφ, hg, hAc]
  have hqN : ∀ A ∉ F, Polynomial.X ^ m ∣ φ (hiltonQ n A) := by
    intro A hA
    rw [hiltonQ, map_mul, map_pow, hiltonPi, hprod, hPi_card]
    have hAcS : Aᶜ ∉ S := by simpa [hS] using hA
    rw [Finset.erase_eq_of_notMem (fun h => hAcS (Finset.mem_of_mem_erase h))]
    by_cases hAc : Aᶜ ∈ F
    · have hAS : A ∈ S := by simpa [hS] using hAc
      rw [Finset.card_erase_of_mem hAS, hcnt]
      simp only [hφ, MvPolynomial.eval₂Hom_X', hg, if_pos hAc]
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)
    · have hAS : A ∉ S := by simpa [hS] using hAc
      rw [Finset.erase_eq_of_notMem hAS, hcnt]
      simp only [hφ, MvPolynomial.eval₂Hom_X', hg, if_neg hAc]
      simp
  set D1 : Matrix (Finset (Fin n)) (Finset (Fin n)) (Polynomial ℚ) :=
    Matrix.diagonal (fun C => if C ∈ F then 1 else 0) with hD1
  have hNm : φ.mapMatrix (Matrix.diagonal (hiltonQ n) + hiltonS n • hiltonCompl _ n) =
      Matrix.diagonal (fun C => φ (hiltonQ n C)) + φ (hiltonS n) • hiltonCompl (Polynomial ℚ) n := by
    ext A B
    simp [RingHom.mapMatrix_apply, Matrix.diagonal_apply, hiltonCompl, apply_ite φ]
  have hdiv : ∀ A B, ∃ e, (Matrix.diagonal (fun C => φ (hiltonQ n C)) + φ (hiltonS n) • hiltonCompl (Polynomial ℚ) n) A B
      - Polynomial.X ^ (m - 1) * D1 A B = Polynomial.X ^ m * e := by
    intro A B
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, hD1, hiltonCompl,
      Matrix.of_apply, smul_eq_mul, hs_im]
    by_cases hAB : A = B
    · subst hAB
      by_cases hA : A ∈ F
      · simp only [if_pos hA, hqF A hA, ↓reduceIte]
        exact ⟨if A = Aᶜ then 1 else 0, by ring⟩
      · simp only [if_neg hA, ↓reduceIte]
        obtain ⟨c, hc⟩ := hqN A hA
        exact ⟨c + (if A = Aᶜ then 1 else 0), by rw [hc]; ring⟩
    · simp only [if_neg hAB]
      exact ⟨if A = Bᶜ then 1 else 0, by ring⟩
  choose E hE using hdiv
  have hN'eq : Matrix.diagonal (fun C => φ (hiltonQ n C)) + φ (hiltonS n) • hiltonCompl (Polynomial ℚ) n =
      (Polynomial.X : Polynomial ℚ) ^ (m - 1) • (D1 + (Polynomial.X : Polynomial ℚ) • Matrix.of E) := by
    refine Matrix.ext (fun A B => ?_)
    have h := hE A B
    have hmm : (Polynomial.X : Polynomial ℚ) ^ m = Polynomial.X ^ (m - 1) * Polynomial.X := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hmm] at h
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul] at h ⊢
    linear_combination h
  have hmap : φ.mapMatrix (hiltonMat n) =
      (Polynomial.X : Polynomial ℚ) ^ (m - 1) • (hiltonMobius _ n * (D1 + (Polynomial.X : Polynomial ℚ) • Matrix.of E) * hiltonZeta _ n) := by
    rw [hiltonMat, map_mul, map_mul, hilton_mobius_map, hilton_zeta_map, hNm, hN'eq, Matrix.mul_smul, Matrix.smul_mul]
  intro hdet
  have h1 := congrArg φ hdet
  rw [RingHom.map_det, map_zero] at h1
  have hsub : φ.mapMatrix ((hiltonMat n).submatrix (fun x : F => (x : Finset (Fin n)))
      (fun x : F => (x : Finset (Fin n)))) = (φ.mapMatrix (hiltonMat n)).submatrix
      (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n))) := rfl
  rw [hsub, hmap] at h1
  set W := hiltonMobius _ n * (D1 + (Polynomial.X : Polynomial ℚ) • Matrix.of E) * hiltonZeta _ n with hWdef
  have hsm : ((Polynomial.X : Polynomial ℚ) ^ (m - 1) • W).submatrix
      (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n))) =
      (Polynomial.X : Polynomial ℚ) ^ (m - 1) • W.submatrix
      (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n))) := rfl
  rw [hsm, Matrix.det_smul] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · exact pow_ne_zero _ (pow_ne_zero _ Polynomial.X_ne_zero) h
  · have h2 := congrArg (Polynomial.evalRingHom 0) h
    rw [RingHom.map_det, map_zero] at h2
    have hD1m : (Polynomial.evalRingHom 0).mapMatrix (D1 + (Polynomial.X : Polynomial ℚ) • Matrix.of E) =
        Matrix.diagonal (fun C => if C ∈ F then (1 : ℚ) else 0) := by
      refine Matrix.ext (fun A B => ?_)
      by_cases hAB : A = B
      · subst hAB
        by_cases hA : A ∈ F <;> simp [hD1, RingHom.mapMatrix_apply, hA]
      · simp [hD1, RingHom.mapMatrix_apply, Matrix.diagonal_apply, hAB]
    have hW : (Polynomial.evalRingHom 0).mapMatrix
        ((hiltonMobius _ n * (D1 + (Polynomial.X : Polynomial ℚ) • Matrix.of E) * hiltonZeta _ n).submatrix
          (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n)))) =
        (hiltonMobius ℚ n).submatrix (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n))) *
        (hiltonZeta ℚ n).submatrix (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n))) := by
      have : (Polynomial.evalRingHom 0).mapMatrix
          ((hiltonMobius _ n * (D1 + (Polynomial.X : Polynomial ℚ) • Matrix.of E) * hiltonZeta _ n).submatrix
            (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n)))) =
          ((Polynomial.evalRingHom 0).mapMatrix
            (hiltonMobius _ n * (D1 + (Polynomial.X : Polynomial ℚ) • Matrix.of E) * hiltonZeta _ n)).submatrix
            (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n))) := rfl
      rw [this, map_mul, map_mul, hilton_mobius_map, hilton_zeta_map, hD1m]
      refine Matrix.ext (fun a b => ?_)
      rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
      simp_rw [Matrix.mul_diagonal, Matrix.submatrix_apply]
      simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      exact (Finset.sum_coe_sort F (fun C => hiltonMobius ℚ n a C * hiltonZeta ℚ n C b)).symm
    rw [hW, Matrix.det_mul] at h2
    have hd1 : ((hiltonMobius ℚ n).submatrix (fun x : F => (x : Finset (Fin n)))
        (fun x : F => (x : Finset (Fin n)))).det = 1 := by
      apply hilton_det_unitri
      · intro a b hab
        simp [hiltonMobius, hab]
      · intro a
        simp [hiltonMobius]
    have hd2 : ((hiltonZeta ℚ n).submatrix (fun x : F => (x : Finset (Fin n)))
        (fun x : F => (x : Finset (Fin n)))).det = 1 := by
      apply hilton_det_unitri
      · intro a b hab
        simp [hiltonZeta, hab]
      · intro a
        simp [hiltonZeta]
    rw [hd1, hd2] at h2
    norm_num at h2

theorem hilton_pi_compl (n : ℕ) (A : Finset (Fin n)) : hiltonPi n Aᶜ = hiltonPi n A := by
  unfold hiltonPi
  rw [compl_compl, Finset.erase_right_comm]

theorem hilton_factor (k : ℕ) : ∃ (X : Matrix (Finset (Fin (k + 1))) (Fin (2 ^ (k + 1 - 1)))
      (MvPolynomial (Finset (Fin (k + 1))) ℚ))
    (Y : Matrix (Fin (2 ^ (k + 1 - 1))) (Finset (Fin (k + 1))) (MvPolynomial (Finset (Fin (k + 1))) ℚ)),
    X * Y = Matrix.diagonal (hiltonQ (k + 1)) + hiltonS (k + 1) • hiltonCompl _ (k + 1) := by
  classical
  set T := {r : Finset (Fin (k + 1)) // (0 : Fin (k + 1)) ∉ r}
  have hcard : Fintype.card T = 2 ^ (k + 1 - 1) := by
    rw [Fintype.card_subtype]
    have : Finset.univ.filter (fun r : Finset (Fin (k + 1)) => (0 : Fin (k + 1)) ∉ r) =
        (Finset.univ.erase (0 : Fin (k + 1))).powerset := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
      constructor
      · intro h x hx
        exact Finset.mem_erase.mpr ⟨fun e => h (e ▸ hx), Finset.mem_univ _⟩
      · intro h h0
        exact (Finset.mem_erase.mp (h h0)).1 rfl
    rw [this, Finset.card_powerset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  set e : T ≃ Fin (2 ^ (k + 1 - 1)) := Fintype.equivFinOfCardEq hcard
  have hne : ∀ A : Finset (Fin (k + 1)), A ≠ Aᶜ := by
    intro A h
    by_cases h0 : (0 : Fin (k + 1)) ∈ A
    · have : (0 : Fin (k + 1)) ∈ Aᶜ := h ▸ h0
      exact (Finset.mem_compl.mp this) h0
    · have : (0 : Fin (k + 1)) ∉ Aᶜ := h ▸ h0
      exact this (Finset.mem_compl.mpr h0)
  let rep : Finset (Fin (k + 1)) → T := fun A =>
    if h : (0 : Fin (k + 1)) ∈ A then ⟨Aᶜ, by simpa using h⟩ else ⟨A, h⟩
  have hrep : ∀ A (r : T), (A = r.1 ∨ A = r.1ᶜ) ↔ r = rep A := by
    intro A r
    obtain ⟨r, hr⟩ := r
    simp only [rep]
    by_cases h0 : (0 : Fin (k + 1)) ∈ A
    · rw [dif_pos h0]
      constructor
      · rintro (h | h)
        · exact absurd (h ▸ h0) hr
        · exact Subtype.ext (by simp [h])
      · intro h
        right
        have := congrArg Subtype.val h
        simp only at this
        rw [this, compl_compl]
    · rw [dif_neg h0]
      constructor
      · rintro (h | h)
        · exact Subtype.ext h.symm
        · exfalso
          apply h0
          rw [h]
          exact Finset.mem_compl.mpr hr
      · intro h
        left
        exact (congrArg Subtype.val h).symm
  have hrepv : ∀ A, ((rep A).1 = A ∨ (rep A).1 = Aᶜ) := by
    intro A
    simp only [rep]
    split_ifs <;> simp
  let X0 : Matrix (Finset (Fin (k + 1))) T (MvPolynomial (Finset (Fin (k + 1))) ℚ) :=
    Matrix.of fun A r => if A = r.1 ∨ A = r.1ᶜ then MvPolynomial.X A else 0
  let Y0 : Matrix T (Finset (Fin (k + 1))) (MvPolynomial (Finset (Fin (k + 1))) ℚ) :=
    Matrix.of fun r B => if B = r.1 ∨ B = r.1ᶜ then MvPolynomial.X B * hiltonPi (k + 1) r.1 else 0
  refine ⟨X0.submatrix id e.symm, Y0.submatrix e.symm id, ?_⟩
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hs_split : ∀ A : Finset (Fin (k + 1)),
      hiltonS (k + 1) = MvPolynomial.X A * MvPolynomial.X Aᶜ * hiltonPi (k + 1) A := by
    intro A
    unfold hiltonS hiltonPi
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ A),
      ← Finset.mul_prod_erase (Finset.univ.erase A) _
        (Finset.mem_erase.mpr ⟨(hne A).symm, Finset.mem_univ _⟩)]
    ring
  refine Matrix.ext (fun A B => ?_)
  rw [Matrix.mul_apply]
  simp only [X0, Y0, Matrix.of_apply, ite_mul, zero_mul]
  simp only [hrep A]
  rw [Finset.sum_eq_single (rep A) (fun r _ hr => by rw [if_neg hr]) (by simp), if_pos rfl]
  have hPi_rep : hiltonPi (k + 1) (rep A).1 = hiltonPi (k + 1) A := by
    rcases hrepv A with h | h <;> rw [h]
    exact hilton_pi_compl _ A
  have hBorb : (B = (rep A).1 ∨ B = (rep A).1ᶜ) ↔ (B = A ∨ B = Aᶜ) := by
    rcases hrepv A with h | h <;> rw [h]
    rw [compl_compl, or_comm]
  rw [hPi_rep, if_congr hBorb rfl rfl]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, hiltonCompl, Matrix.of_apply,
    smul_eq_mul, hiltonQ]
  by_cases h1 : B = A
  · subst h1
    have : B ≠ Bᶜ := hne B
    simp [this]
    ring
  · by_cases h2 : B = Aᶜ
    · subst h2
      have : A ≠ Aᶜ := hne A
      simp [this, Ne.symm this, hs_split A]
      ring
    · have h3 : A ≠ Bᶜ := fun h => h2 (by rw [h, compl_compl])
      simp [h1, h2, h3, Ne.symm h1]

theorem hilton_lift {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    (L0 : Matrix (Finset (Fin n)) (Fin (2 ^ (n - 1))) R) (R0 : Matrix (Fin (2 ^ (n - 1))) (Finset (Fin n)) R)
    (hz : ∀ A B : Finset (Fin n), ¬ A ⊆ B → ¬ B ⊆ A → (L0 * R0) A B = 0)
    (hd : ∀ F : Finset (Finset (Fin n)), is_uncomplemented F →
        ((L0 * R0).submatrix (fun x : F => (x : Finset (Fin n)))
          (fun x : F => (x : Finset (Fin n)))).det ≠ 0) :
    ∃ (K : Type) (_ : Field K) (L : Matrix (Finset (Fin n)) (Fin (2 ^ (n - 1))) K)
      (R : Matrix (Fin (2 ^ (n - 1))) (Finset (Fin n)) K),
      (∀ A B : Finset (Fin n), ¬ A ⊆ B → ¬ B ⊆ A → (L * R) A B = 0) ∧
      ∀ F : Finset (Finset (Fin n)), is_uncomplemented F →
        ((L * R).submatrix (fun x : F => (x : Finset (Fin n)))
          (fun x : F => (x : Finset (Fin n)))).det ≠ 0 := by
  refine ⟨FractionRing R, inferInstance, L0.map (algebraMap R (FractionRing R)),
    R0.map (algebraMap R (FractionRing R)), ?_, ?_⟩
  · intro A B h1 h2
    rw [← Matrix.map_mul, Matrix.map_apply, hz A B h1 h2, map_zero]
  · intro F hF
    rw [← Matrix.map_mul]
    have : ((L0 * R0).map (algebraMap R (FractionRing R))).submatrix
        (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n))) =
        (algebraMap R (FractionRing R)).mapMatrix ((L0 * R0).submatrix
          (fun x : F => (x : Finset (Fin n))) (fun x : F => (x : Finset (Fin n)))) := rfl
    rw [this, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr (hd F hF)

/-- The matrix of Theorem 2.1: rank at most 2^(n-1) (as a product through 2^(n-1) dimensions), zero on incomparable pairs, nonsingular on every uncomplemented family. -/
theorem hilton_strong_incomparability_matrix (n : ℕ) :
    ∃ (K : Type) (_ : Field K) (L : Matrix (Finset (Fin n)) (Fin (2 ^ (n - 1))) K)
      (R : Matrix (Fin (2 ^ (n - 1))) (Finset (Fin n)) K),
      (∀ A B : Finset (Fin n), ¬ A ⊆ B → ¬ B ⊆ A → (L * R) A B = 0) ∧
      ∀ F : Finset (Finset (Fin n)), is_uncomplemented F →
        ((L * R).submatrix (fun x : F => (x : Finset (Fin n)))
          (fun x : F => (x : Finset (Fin n)))).det ≠ 0 := by
  classical
  rcases n with _ | k
  · refine ⟨ℚ, inferInstance, 0, 0, fun A B h _ => absurd (Subsingleton.elim A B ▸ subset_refl A) h,
      fun F hF => ?_⟩
    have hF0 : F = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro A hA
      exact hF A hA (by rwa [Subsingleton.elim Aᶜ A])
    have : IsEmpty F := Finset.isEmpty_coe_sort.mpr hF0
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · obtain ⟨X, Y, hXY⟩ := hilton_factor k
    have hLR : (hiltonMobius (MvPolynomial (Finset (Fin (k + 1))) ℚ) (k + 1) * X) *
        (Y * hiltonZeta (MvPolynomial (Finset (Fin (k + 1))) ℚ) (k + 1)) = hiltonMat (k + 1) := by
      rw [hiltonMat, Matrix.mul_assoc (hiltonMobius _ _) X, ← Matrix.mul_assoc X, hXY, ← Matrix.mul_assoc]
    refine hilton_lift (hiltonMobius (MvPolynomial (Finset (Fin (k + 1))) ℚ) (k + 1) * X)
      (Y * hiltonZeta (MvPolynomial (Finset (Fin (k + 1))) ℚ) (k + 1)) ?_ ?_
    · intro A B h1 h2
      rw [hLR, hiltonMat]
      exact hilton_mat_zero_of_incomparable _ _ A B h1 h2
    · intro F hF
      rw [hLR]
      exact hilton_mat_det_ne F hF
