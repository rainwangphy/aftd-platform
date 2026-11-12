import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# rank_one_qutrit_compression_three_binary_parent

Topic: quantum   Node: 2b708f8a8a9a

Provenance: helper lemma. Local compatibility helper for OP-693.

Every three binary qutrit effects have a positive joint parent after compression to any subspace of dimension at most one.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false

private lemma in767_rankoneproof_projection_eigenvalues (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) (k : Fin 3) :
    hP.eigenvalues k = 0 ∨ hP.eigenvalues k = 1 := by
  let v : Fin 3 → ℂ := ⇑(hP.eigenvectorBasis k)
  have hv : v ≠ 0 := by
    intro h
    apply hP.eigenvectorBasis.orthonormal.ne_zero k
    apply WithLp.ofLp_injective 2
    exact h
  have he : P *ᵥ v = (hP.eigenvalues k : ℂ) • v := by
    simpa [RCLike.real_smul_eq_coe_smul] using hP.mulVec_eigenvectorBasis k
  have hh : (hP.eigenvalues k : ℂ) • ((hP.eigenvalues k : ℂ) • v) =
      (hP.eigenvalues k : ℂ) • v := by
    calc
      _ = P *ᵥ (P *ᵥ v) := by rw [he, Matrix.mulVec_smul, he]
      _ = (P*P) *ᵥ v := Matrix.mulVec_mulVec v P P
      _ = P *ᵥ v := by rw [hPP]
      _ = _ := he
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := by simpa using hi
  have hcoord := congrFun hh i
  simp only [Pi.smul_apply, smul_eq_mul] at hcoord
  have hz : ((hP.eigenvalues k : ℂ)^2 - (hP.eigenvalues k : ℂ)) * v i = 0 := by
    linear_combination hcoord
  have heval : (hP.eigenvalues k : ℝ)^2 - hP.eigenvalues k = 0 := by
    have h := (mul_eq_zero.mp hz).resolve_right hi'
    exact_mod_cast h
  have hfactor : hP.eigenvalues k * (hP.eigenvalues k - 1)=0 := by nlinarith [heval]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

private lemma in767_rankoneproof_projection_rank_isometry
    (k : ℕ) (P : Matrix (Fin 3) (Fin 3) ℂ) (hP : P.IsHermitian) (hPP : P*P=P) (hRank : P.rank=k) :
    ∃ U : Matrix (Fin 3) (Fin k) ℂ, Uᴴ*U=1 ∧ U*Uᴴ=P := by
  classical
  let I := {k : Fin 3 // hP.eigenvalues k ≠ 0}
  have hcard : Fintype.card I = k := by
    change Fintype.card {k : Fin 3 // hP.eigenvalues k ≠ 0} = k
    rw [← hP.rank_eq_card_non_zero_eigs]
    exact hRank
  let e : Fin k ≃ I := Fintype.equivOfCardEq (by simp [hcard])
  let V : Matrix (Fin 3) (Fin 3) ℂ := hP.eigenvectorUnitary
  let U : Matrix (Fin 3) (Fin k) ℂ := fun i j => V i (e j).val
  have hV : Vᴴ*V=1 := by
    have hh := Unitary.coe_star_mul_self hP.eigenvectorUnitary
    simpa [V, Matrix.star_eq_conjTranspose] using hh
  have hU : Uᴴ*U=1 := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M (e i).val (e j).val) hV
    have heq : (e i).val = (e j).val ↔ i=j := by
      constructor
      · intro h
        exact e.injective (Subtype.ext h)
      · rintro rfl
        rfl
    simpa [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, heq] using hh
  have hspec : P = V * Matrix.diagonal (fun k => (hP.eigenvalues k : ℂ)) * Vᴴ := by
    have hh := hP.spectral_theorem
    simpa [V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using hh
  have heig (k : Fin 3) : hP.eigenvalues k = 0 ∨ hP.eigenvalues k = 1 :=
    in767_rankoneproof_projection_eigenvalues P hP hPP k
  have hterm (i j k : Fin 3) :
      V i k * (hP.eigenvalues k : ℂ) * star (V j k) =
      if hP.eigenvalues k ≠ 0 then V i k * star (V j k) else 0 := by
    rcases heig k with h | h <;> simp [h]
  have hsub (i j : Fin 3) :
      (∑ k : Fin 3, if hP.eigenvalues k ≠ 0 then V i k * star (V j k) else 0) =
      ∑ k : I, V i k.val * star (V j k.val) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter fun k : Fin 3 => hP.eigenvalues k ≠ 0) (by simp) _
  have hUU : U*Uᴴ=P := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hspec
    rw [Matrix.mul_apply] at hh
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply] at hh
    simp_rw [hterm] at hh
    rw [hsub] at hh
    have he := e.sum_comp (fun k : I => V i k.val * star (V j k.val))
    change (∑ k : Fin k, V i (e k).val * star (V j (e k).val)) = P i j
    rw [he]
    exact hh.symm
  exact ⟨U,hU,hUU⟩



private noncomputable def in767_rankoneproof_probability_weight (p : Fin 3 → ℝ) (s : Fin 3 → Bool) : ℝ :=
  ∏ j, if s j then p j else 1-p j

private lemma in767_rankoneproof_probability_weight_nonneg (p : Fin 3 → ℝ)
    (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (s : Fin 3 → Bool) :
    0 ≤ in767_rankoneproof_probability_weight p s := by
  apply Finset.prod_nonneg
  intro j hj
  split <;> linarith [hp j]

private lemma in767_rankoneproof_probability_weight_sum (p : Fin 3 → ℝ) :
    (∑ s : Fin 3 → Bool, in767_rankoneproof_probability_weight p s) = 1 := by
  have hh := Finset.sum_prod_piFinset (ι := Fin 3) (Finset.univ : Finset Bool)
    (fun j b => if b then p j else 1-p j)
  simp only [Fintype.piFinset_univ] at hh
  simpa [in767_rankoneproof_probability_weight, Fintype.sum_bool] using hh

private lemma in767_rankoneproof_probability_weight_marginal (p : Fin 3 → ℝ) (j : Fin 3) :
    (∑ s : Fin 3 → Bool, if s j then in767_rankoneproof_probability_weight p s else 0) = p j := by
  let f : Fin 3 → Bool → ℝ := fun i b => if i=j then if b then p i else 0 else if b then p i else 1-p i
  have hprod (s : Fin 3 → Bool) : (∏ i, f i (s i)) =
      if s j then in767_rankoneproof_probability_weight p s else 0 := by
    fin_cases j <;> cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
      simp [f, in767_rankoneproof_probability_weight, Fin.prod_univ_three, h0,h1,h2]
  have hh := Finset.sum_prod_piFinset (ι := Fin 3) (Finset.univ : Finset Bool) f
  simp only [Fintype.piFinset_univ] at hh
  simp_rw [hprod] at hh
  fin_cases j <;> simp [f, Fintype.sum_bool, Fin.prod_univ_three] at hh ⊢ <;> linarith

private lemma in767_rankoneproof_hidden_model_parent
    (n m : ℕ) (Q : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (p : Fin 3 → Fin m → ℝ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hQ : ∀ t, (Q t).PosSemidef) (hsum : (∑ t, Q t)=P)
    (hp : ∀ j t, 0 ≤ p j t ∧ p j t ≤ 1) :
    ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t := by
  let G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ := fun s =>
    ∑ t, in767_rankoneproof_probability_weight (fun j => p j t) s • Q t
  refine ⟨G, ?_, ?_, ?_⟩
  · intro s
    change (∑ t, in767_rankoneproof_probability_weight (fun j => p j t) s • Q t).PosSemidef
    have H (T : Finset (Fin m)) : (∑ t ∈ T, in767_rankoneproof_probability_weight (fun j => p j t) s • Q t).PosSemidef := by
      induction T using Finset.induction_on with
      | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
      | @insert t T ht ih =>
        rw [Finset.sum_insert ht]
        exact ((hQ t).smul (in767_rankoneproof_probability_weight_nonneg _ (fun j => hp j t) s)).add ih
    exact H Finset.univ
  · change (∑ s, ∑ t, in767_rankoneproof_probability_weight (fun j => p j t) s • Q t) = P
    rw [Finset.sum_comm]
    calc
      (∑ t, ∑ s, in767_rankoneproof_probability_weight (fun j => p j t) s • Q t) =
          ∑ t, (∑ s, in767_rankoneproof_probability_weight (fun j => p j t) s) • Q t := by simp [Finset.sum_smul]
      _ = ∑ t, Q t := by simp [in767_rankoneproof_probability_weight_sum]
      _ = P := hsum
  · intro j
    change (∑ s, if s j then (∑ t, in767_rankoneproof_probability_weight (fun k => p k t) s • Q t) else 0) = _
    have heq (s : Fin 3 → Bool) :
        (if s j then (∑ t, in767_rankoneproof_probability_weight (fun k => p k t) s • Q t) else 0) =
        ∑ t, (if s j then in767_rankoneproof_probability_weight (fun k => p k t) s else 0) • Q t := by
      cases hs : s j <;> simp [hs]
    simp_rw [heq]
    rw [Finset.sum_comm]
    calc
      (∑ t, ∑ s, (if s j then in767_rankoneproof_probability_weight (fun k => p k t) s else 0) • Q t) =
          ∑ t, (∑ s, if s j then in767_rankoneproof_probability_weight (fun k => p k t) s else 0) • Q t := by simp [Finset.sum_smul]
      _ = ∑ t, (p j t) • Q t := by simp [in767_rankoneproof_probability_weight_marginal]


private lemma in767_rankoneproof_rank_one_parent (M : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hM : ∀ j, (M j).PosSemidef ∧ (1 - M j).PosSemidef)
    (hP : P.IsHermitian) (hPP : P*P=P) (hr : P.rank ≤ 1) :
    ∃ G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) = P * M j * P := by
  classical
  rcases Nat.eq_zero_or_pos P.rank with hzero | hpos
  · obtain ⟨U,hU,hUU⟩ := in767_rankoneproof_projection_rank_isometry 0 P hP hPP hzero
    have hPzero : P=0 := by
      rw [← hUU]
      ext i j
      simp [Matrix.mul_apply]
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro s
      exact Matrix.PosSemidef.zero
    · simp [hPzero]
    · intro j
      simp [hPzero]
  · have hrank : P.rank=1 := by omega
    obtain ⟨U,hU,hUU⟩ := in767_rankoneproof_projection_rank_isometry 1 P hP hPP hrank
    let v : Fin 3 → ℂ := fun i => U i 0
    have hv : star v ⬝ᵥ v = 1 := by
      have hh := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A 0 0) hU
      simpa [v, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct] using hh
    have hPvv : P = Matrix.vecMulVec v (star v) := by
      rw [← hUU]
      ext i j
      simp [v, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply]
    let p : Fin 3 → Fin 1 → ℝ := fun j _ => (star v ⬝ᵥ (M j *ᵥ v)).re
    have hp (j : Fin 3) (t : Fin 1) : 0 ≤ p j t ∧ p j t ≤ 1 := by
      have ha := (hM j).1.dotProduct_mulVec_nonneg v
      have hb := (hM j).2.dotProduct_mulVec_nonneg v
      have ha' := (Complex.nonneg_iff.mp ha).1
      have hb' := (Complex.nonneg_iff.mp hb).1
      have hb'' : (star v ⬝ᵥ ((1 - M j) *ᵥ v)).re =
          1 - (star v ⬝ᵥ (M j *ᵥ v)).re := by
        simp [Matrix.sub_mulVec, dotProduct_sub, hv]
      dsimp [p]
      constructor
      · exact ha'
      · rw [hb''] at hb'
        linarith
    have hp_eq (j : Fin 3) : ((p j 0 : ℝ) : ℂ) = star v ⬝ᵥ (M j *ᵥ v) := by
      have ha := (hM j).1.dotProduct_mulVec_nonneg v
      have ha' := (Complex.nonneg_iff.mp ha).2
      apply Complex.ext <;> simp [p, ha']
    have houter (j : Fin 3) : P * M j * P = (p j 0) • P := by
      rw [hPvv]
      apply Matrix.ext
      intro i k
      simp only [Matrix.smul_apply, Complex.real_smul, hp_eq]
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec,
        Fin.sum_univ_three, Pi.star_apply]
      ring
    have hPpos : P.PosSemidef := by
      rw [← hUU]
      exact Matrix.posSemidef_self_mul_conjTranspose U
    obtain ⟨G,hG,hGsum,hGmarg⟩ := in767_rankoneproof_hidden_model_parent 3 1 (fun _ => P) p P
      (fun _ => hPpos) (by simp) hp
    refine ⟨G,hG,hGsum,?_⟩
    intro j
    rw [hGmarg j]
    simpa using (houter j).symm

theorem rank_one_qutrit_compression_three_binary_parent :
  ∀ (M : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ) (P : Matrix (Fin 3) (Fin 3) ℂ),
    (∀ j, (M j).PosSemidef ∧ (1-M j).PosSemidef) →
    P.IsHermitian → P*P=P → P.rank ≤ 1 →
    ∃ G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) = P*M j*P := by
  exact in767_rankoneproof_rank_one_parent
