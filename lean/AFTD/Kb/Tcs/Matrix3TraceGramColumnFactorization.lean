import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TraceSplitReconstruction

/-!
# matrix3_trace_gram_column_factorization

Topic: algebraic_complexity   Node: 90a1ea642e8b

Provenance: formalization of a published result. Source: arXiv:2610.11823v3, Section 4.2, equation (4.2), including both column-space restrictions. This formalization works over every field; the minus sign outside characteristic two is absorbed into L. The split-map proof and the extension of coefficient maps are written here, with no external rank bounds or computation certificates assumed.

For a cyclic trace decomposition over a field whose first-factor matrix ranks sum to 27+d, there are 3-by-d matrices L_t and M_s such that a_t b_s c_t a_s equals the diagonal term (a_s if t=s, zero otherwise) plus L_t times the transpose of M_s. Every column of L_t is in the column space of a_t, and every column of M_s is in the column space of the transpose of a_s.
-/

open Matrix Finset
noncomputable section
variable {K : Type*} [Field K] {r : ℕ}

private abbrev matrix3_gram_space (a : Fin r → Matrix (Fin 3) (Fin 3) K) :=
  ∀ s, LinearMap.range (a s).mulVecLin

private def matrix3_gram_map (a b : Fin r → Matrix (Fin 3) (Fin 3) K) :
    matrix3_gram_space a →ₗ[K] (Fin 3 × Fin 3 × Fin 3 → K) where
  toFun x p := ∑ s, (x s).val p.1 * b s p.2.1 p.2.2
  map_add' x y := by
    ext p
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    ext p
    simp [Finset.mul_sum, mul_assoc]

private def matrix3_gram_preimage (a c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (z : Fin 3 × Fin 3 × Fin 3 → K) : matrix3_gram_space a :=
  fun s => ⟨(a s).mulVecLin (fun j => ∑ k, ∑ i, c s k i * z (i,j,k)),
    ⟨_, rfl⟩⟩

private theorem matrix3_gram_reconstruction (a b c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0)
    (z : Fin 3 × Fin 3 × Fin 3 → K) :
    matrix3_gram_map a b (matrix3_gram_preimage a c z) = z := by
  ext p
  exact matrix3_trace_split_reconstruction a b c h z p
end

set_option backward.isDefEq.respectTransparency false in
theorem matrix3_trace_gram_column_factorization {K : Type*} [Field K] {r d : ℕ}
    (a b c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0)
    (hd : ∑ s, (a s).rank = 27 + d) :
    ∃ L M : Fin r → Matrix (Fin 3) (Fin d) K,
      (∀ t s, a t * b s * c t * a s =
        (if t = s then a s else 0) + L t * (M s)ᵀ) ∧
      (∀ t q, (L t).col q ∈ LinearMap.range (a t).mulVecLin) ∧
      (∀ s q, (M s).col q ∈ LinearMap.range (a s)ᵀ.mulVecLin) := by
  classical
  let X := matrix3_gram_map a b
  letI : Module.Free K (LinearMap.ker X) :=
    @Module.Free.of_divisionRing K (LinearMap.ker X) (inferInstance : DivisionRing K)
      (inferInstance : AddCommGroup (LinearMap.ker X))
      (inferInstance : Module K (LinearMap.ker X))
  have hsur : Function.Surjective X := fun z =>
    ⟨matrix3_gram_preimage a c z, matrix3_gram_reconstruction a b c h z⟩
  have hdimE : Module.finrank K (matrix3_gram_space a) = 27 + d := by
    simpa [matrix3_gram_space, Module.finrank_pi_fintype, Matrix.rank] using hd
  have hdimR : Module.finrank K (LinearMap.range X) = 27 := by
    rw [LinearMap.range_eq_top.mpr hsur, finrank_top]
    norm_num [Module.finrank_pi]
  have hdimN : Module.finrank K (LinearMap.ker X) = d := by
    have he := LinearMap.finrank_range_add_finrank_ker X
    rw [hdimR, hdimE] at he
    omega
  let B : Module.Basis (Fin d) K (LinearMap.ker X) :=
    (Module.finBasis K (LinearMap.ker X)).reindex (finCongr hdimN)
  let P (x : matrix3_gram_space a) : LinearMap.ker X :=
    ⟨x - matrix3_gram_preimage a c (X x), by
      rw [LinearMap.mem_ker, map_sub]
      change X x - matrix3_gram_map a b (matrix3_gram_preimage a c (X x)) = 0
      rw [matrix3_gram_reconstruction a b c h, sub_self]⟩
  let v (s : Fin r) (j : Fin 3) : LinearMap.range (a s).mulVecLin :=
    ⟨(a s).col j, ⟨Pi.single j 1, by simp⟩⟩
  let z (s : Fin r) (j : Fin 3) : matrix3_gram_space a := Pi.single s (v s j)
  let Y : (Fin 3 × Fin 3 × Fin 3 → K) →ₗ[K] matrix3_gram_space a :=
    { toFun := matrix3_gram_preimage a c
      map_add' := by
        intro x y
        funext s
        apply Subtype.ext
        change (a s).mulVecLin (fun j => ∑ k, ∑ i, c s k i * (x + y) (i,j,k)) =
          (a s).mulVecLin (fun j => ∑ k, ∑ i, c s k i * x (i,j,k)) +
          (a s).mulVecLin (fun j => ∑ k, ∑ i, c s k i * y (i,j,k))
        rw [← map_add]
        congr 1
        ext j
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro u x
        funext s
        apply Subtype.ext
        change (a s).mulVecLin (fun j => ∑ k, ∑ i, c s k i * (u • x) (i,j,k)) =
          u • (a s).mulVecLin (fun j => ∑ k, ∑ i, c s k i * x (i,j,k))
        rw [← map_smul]
        congr 1
        ext j
        simp [Finset.mul_sum, mul_assoc, mul_left_comm] }
  let PN : matrix3_gram_space a →ₗ[K] LinearMap.ker X :=
    { toFun := P
      map_add' := by
        intro x y
        apply Subtype.ext
        change x + y - Y (X (x + y)) = (x - Y (X x)) + (y - Y (X y))
        rw [map_add, map_add]
        abel
      map_smul' := by
        intro u x
        apply Subtype.ext
        change u • x - Y (X (u • x)) = u • (x - Y (X x))
        simp only [map_smul, smul_sub] }
  let S (s : Fin r) : LinearMap.range (a s).mulVecLin →ₗ[K] matrix3_gram_space a :=
    { toFun := fun v => (Pi.single s v : matrix3_gram_space a)
      map_add' := by intros; simp [Pi.single_add]
      map_smul' := by intros; simp [Pi.single_smul] }
  let D (s : Fin r) : LinearMap.range (a s).mulVecLin →ₗ[K] (Fin d → K) :=
    B.equivFun.toLinearMap.comp (PN.comp (S s))
  choose G hG using fun s => (D s).exists_extend
  let L : Fin r → Matrix (Fin 3) (Fin d) K := fun t i q => -((B q).val t).val i
  let M : Fin r → Matrix (Fin 3) (Fin d) K := fun s => ((G s).toMatrix' * a s)ᵀ
  have hM (s : Fin r) (j : Fin 3) (q : Fin d) :
      M s j q = B.repr (P (z s j)) q := by
    have he := congrArg (fun f : LinearMap.range (a s).mulVecLin →ₗ[K] (Fin d → K) =>
      f (v s j) q) (hG s)
    change (G s) ((a s).col j) q = B.equivFun (P (z s j)) q at he
    rw [Module.Basis.equivFun_apply] at he
    change ((G s).toMatrix' * a s) q j = _
    calc
      _ = ((G s).toMatrix' *ᵥ (a s).col j) q := rfl
      _ = (G s) ((a s).col j) q := congrFun ((G s).toMatrix'_mulVec _) q
      _ = _ := he
  refine ⟨L, M, ?_, ?_, ?_⟩
  · intro t s
    ext i j
    have hsimp (p : Fin 3 × Fin 3 × Fin 3) :
        (X (z s j)) p = a s p.1 j * b s p.2.1 p.2.2 := by
      change (∑ q, ((Pi.single s (v s j) : matrix3_gram_space a) q).val p.1 *
        b q p.2.1 p.2.2) = _
      rw [Finset.sum_eq_single s]
      · simp [v]
      · intro q _ hqs
        simp [Pi.single_eq_of_ne hqs]
      · simp
    have he := congrArg (fun x : LinearMap.ker X => (x.val t).val i) (B.sum_repr (P (z s j)))
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul] at he
    change (∑ q, B.repr (P (z s j)) q * ((B q).val t).val i) =
      ((z s j) t).val i - (matrix3_gram_preimage a c (X (z s j)) t).val i at he
    simp_rw [← hM s j] at he
    have hexpand : (a t * b s * c t * a s) i j =
        (matrix3_gram_preimage a c (X (z s j)) t).val i := by
      simp only [matrix3_gram_preimage, mulVecLin_apply, mulVec, dotProduct, hsimp]
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      ring
    have hz : ((z s j) t).val i = ((if t = s then a s else 0) : Matrix (Fin 3) (Fin 3) K) i j := by
      by_cases hts : t = s
      · subst t; simp [z, v]
      · simp [z, v, hts]
    rw [← hexpand, hz] at he
    change (a t * b s * c t * a s) i j =
      ((if t = s then a s else 0) : Matrix (Fin 3) (Fin 3) K) i j +
        ∑ q, L t i q * M s j q
    simp only [L, neg_mul, Finset.sum_neg_distrib]
    simp_rw [mul_comm (M s j _)] at he
    linear_combination he

  · intro t q
    change -((B q).val t).val ∈ LinearMap.range (a t).mulVecLin
    exact (LinearMap.range (a t).mulVecLin).neg_mem ((B q).val t).property
  · intro s q
    refine ⟨fun i => (G s).toMatrix' q i, ?_⟩
    ext j
    change (∑ i, a s i j * (G s).toMatrix' q i) = ∑ i, (G s).toMatrix' q i * a s i j
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
