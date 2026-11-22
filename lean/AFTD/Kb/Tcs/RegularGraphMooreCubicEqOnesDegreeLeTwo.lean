import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.Monomial
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# regular_graph_moore_cubic_eq_ones_degree_le_two

Topic: graphs   Node: 196b90831a6a

Provenance: formalization of a published result. Source: arXiv:2611.26037 (An improved Moore bound for girths seven and eleven), proof of Theorem 3.1, case r(G) = 0: a Moore graph of diameter 3 has degree at most 2 (the paper's reference [23]).

Let H be a finite nonempty d-regular simple graph with adjacency matrix A (over the integers). If A^3 + A^2 - 2(d-1)A - (d-1)I equals the all-ones matrix J, i.e. H is a Moore graph of diameter 3 (every ordered pair of vertices is joined by exactly one non-backtracking walk of length at most 3), then d ≤ 2.
-/

namespace RgMoore3
open Polynomial Matrix

/-- The Moore cubic `X^3 + X^2 - 2zX - z` over a commutative ring. -/
noncomputable def mF (R : Type*) [CommRing R] (z : R) : R[X] := X ^ 3 + X ^ 2 - C (2 * z) * X - C z

lemma mF_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : R) :
    (mF R z).map f = mF S (f z) := by
  simp [mF, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, map_ofNat]

lemma mF_natDegree (R : Type*) [CommRing R] [Nontrivial R] (z : R) : (mF R z).natDegree = 3 := by
  unfold mF; compute_degree!

lemma mF_monic (R : Type*) [CommRing R] [Nontrivial R] (z : R) : (mF R z).Monic := by
  unfold mF; monicity!

lemma mF_eval {R : Type*} [CommRing R] (z x : R) :
    (mF R z).eval x = x ^ 3 + x ^ 2 - 2 * z * x - z := by
  simp [mF]

lemma mF_nextCoeff (R : Type*) [CommRing R] [Nontrivial R] (z : R) : (mF R z).nextCoeff = 1 := by
  rw [nextCoeff, mF_natDegree]; simp [mF]

/-- No integer root for `z ≥ 1`. -/
lemma int_no_root (z : ℤ) (hz : 1 ≤ z) (k : ℤ) : k ^ 3 + k ^ 2 - 2 * z * k - z ≠ 0 := by
  intro h
  have h1 : (2 * k + 1) * (-(4 * k ^ 2 + 2 * k - 1 - 8 * z)) = 1 := by linear_combination (-8) * h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h2 | h2
  · have : k = 0 := by omega
    subst this; nlinarith
  · have : k = -1 := by omega
    subst this; nlinarith

lemma mF_irreducible (z : ℤ) (hz : 1 ≤ z) : Irreducible (mF ℚ (z : ℚ)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot (by rw [mF_natDegree]; decide)
  intro x hx
  have hmon : (mF ℤ z).Monic := mF_monic ℤ z
  have hroot : aeval x (mF ℤ z) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, mF_map]; simpa using hx
  obtain ⟨k, hk⟩ := isInteger_of_is_root_of_monic hmon hroot
  have hk' : (k : ℚ) = x := by simpa using hk
  have : (mF ℚ (z : ℚ)).eval (k : ℚ) = 0 := by rw [hk']; exact hx
  rw [mF_eval] at this
  exact int_no_root z hz k (by exact_mod_cast this)

/-- A monic rational polynomial whose real roots (it splits over ℝ) are all roots of an irreducible
monic `Fq` is a power of `Fq`. -/
lemma eq_pow_of_roots (Fq : ℚ[X]) (hirr : Irreducible Fq) (hmon : Fq.Monic) :
    ∀ (N : ℕ) (G : ℚ[X]), G.natDegree = N → G.Monic → (G.map (algebraMap ℚ ℝ)).Splits →
      (∀ θ ∈ (G.map (algebraMap ℚ ℝ)).roots, aeval θ Fq = 0) → ∃ m, G = Fq ^ m := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro G hN hG hsp hroots
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · exact ⟨0, by rw [pow_zero]; exact Polynomial.eq_one_of_monic_natDegree_zero hG (hN.trans h0)⟩
  have hcard : (G.map (algebraMap ℚ ℝ)).roots.card = N := by
    rw [(splits_iff_card_roots).mp hsp, natDegree_map, hN]
  obtain ⟨θ, hθ⟩ : ∃ θ, θ ∈ (G.map (algebraMap ℚ ℝ)).roots := by
    apply Multiset.card_pos_iff_exists_mem.mp; omega
  have hFθ := hroots θ hθ
  have hGθ : aeval θ G = 0 := by
    have hne : G.map (algebraMap ℚ ℝ) ≠ 0 := (hG.map _).ne_zero
    have := (mem_roots hne).mp hθ
    rwa [IsRoot, eval_map_algebraMap] at this
  have hmin : Fq = minpoly ℚ θ := minpoly.eq_of_irreducible_of_monic hirr hFθ hmon
  have hdvd : Fq ∣ G := hmin ▸ minpoly.dvd ℚ θ hGθ
  obtain ⟨G', rfl⟩ := hdvd
  have hG' : G'.Monic := hmon.of_mul_monic_left hG
  have hdegF : 0 < Fq.natDegree := Irreducible.natDegree_pos hirr
  have hdeg : (Fq * G').natDegree = Fq.natDegree + G'.natDegree := hmon.natDegree_mul hG'
  have hlt : G'.natDegree < N := by omega
  have hmapne : (Fq * G').map (algebraMap ℚ ℝ) ≠ 0 := (hG.map _).ne_zero
  have hdvd' : G'.map (algebraMap ℚ ℝ) ∣ (Fq * G').map (algebraMap ℚ ℝ) :=
    Polynomial.map_dvd _ (dvd_mul_left _ _)
  obtain ⟨m, hm⟩ := ih _ hlt G' rfl hG' (hsp.of_dvd hmapne hdvd') (by
    intro θ' hθ'
    apply hroots θ'
    exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd hmapne hdvd') hθ')
  exact ⟨m + 1, by rw [hm, pow_succ, mul_comm]⟩


lemma aeval_mulVec {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (v : W → ℝ) (μ : ℝ)
    (h : A *ᵥ v = μ • v) (p : ℝ[X]) : (aeval A p) *ᵥ v = p.eval μ • v := by
  have hpow : ∀ k : ℕ, (A ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mulVec, hp, hq, add_smul]
  | monomial n c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mulVec, hpow,
      eval_monomial, smul_smul]

lemma trace_aeval {W : Type*} [Fintype W] [DecidableEq W] {A : Matrix W W ℝ} (hA : A.IsHermitian)
    (p : ℝ[X]) : (aeval A p).trace = ∑ i, p.eval (hA.eigenvalues i) := by
  have hpow : ∀ k : ℕ, (A ^ k).trace = ∑ i, (hA.eigenvalues i) ^ k := by
    intro k
    conv_lhs => rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply, trace_mul_cycle]
    have hu : star (hA.eigenvectorUnitary : Matrix W W ℝ) * (hA.eigenvectorUnitary : Matrix W W ℝ) = 1 :=
      Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2
    rw [hu, one_mul, diagonal_pow, trace_diagonal]
    simp
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib]
  | monomial n c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, trace_smul, hpow]
    simp [eval_monomial, Finset.mul_sum]

theorem moore_cubic (d : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hne : Nonempty W) (hreg : H.IsRegularOfDegree d)
    (hC : ((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2 - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ
        - ((d : ℤ) - 1) • (1 : Matrix W W ℤ) : Matrix W W ℤ) = Matrix.of (fun _ _ => (1 : ℤ))) :
    d ≤ 2 := by
  by_contra hd'
  have hd : 2 < d := Nat.lt_of_not_le hd'
  set A : Matrix W W ℝ := H.adjMatrix ℝ with hAdef
  set z : ℝ := (d : ℝ) - 1 with hz
  set J : Matrix W W ℝ := Matrix.of (fun _ _ => (1 : ℝ)) with hJ
  set n : ℕ := Fintype.card W with hn
  have hnpos : 0 < n := Fintype.card_pos
  -- F(A) = J over ℝ
  have hFA : aeval A (mF ℝ z) = J := by
    have h2 := congrArg (Int.castRingHom ℝ).mapMatrix hC
    have hmapA : (Int.castRingHom ℝ).mapMatrix (H.adjMatrix ℤ) = A := by
      ext u v; simp [A, SimpleGraph.adjMatrix_apply]
    simp only [map_sub, map_add, map_pow, map_zsmul, map_one, hmapA] at h2
    have hJ' : (Int.castRingHom ℝ).mapMatrix (Matrix.of (fun _ _ => (1 : ℤ)) : Matrix W W ℤ) = J := by
      ext u v; simp [J]
    rw [hJ'] at h2
    have e3 : aeval A (mF ℝ z) = A ^ 3 + A ^ 2 - (2 * z) • A - z • (1 : Matrix W W ℝ) := by
      simp [mF, Algebra.algebraMap_eq_smul_one]
      module
    have e4 : (2 * ((d : ℤ) - 1)) • A = (2 * z) • A := by
      rw [← Int.cast_smul_eq_zsmul ℝ]; push_cast; rfl
    have e5 : ((d : ℤ) - 1) • (1 : Matrix W W ℝ) = z • 1 := by
      rw [← Int.cast_smul_eq_zsmul ℝ]; push_cast; rfl
    rw [e3, ← e4, ← e5, h2]
  -- the all-ones vector
  have h1 : A *ᵥ (fun _ => (1 : ℝ)) = (d : ℝ) • (fun _ => (1 : ℝ)) := by
    ext u
    have := SimpleGraph.adjMatrix_mulVec_const_apply (G := H) (a := (1 : ℝ)) (v := u)
    rw [show (A *ᵥ fun _ => (1 : ℝ)) u = (H.adjMatrix ℝ *ᵥ Function.const W (1 : ℝ)) u from rfl,
      this, hreg.degree_eq u]; simp
  have hJv : ∀ v : W → ℝ, J *ᵥ v = (∑ u, v u) • (fun _ => (1 : ℝ)) := by
    intro v; ext u; simp [J, mulVec, dotProduct]
  -- n = F(d)
  have hnF : (n : ℝ) = (mF ℝ z).eval (d : ℝ) := by
    have e1 := aeval_mulVec A _ _ h1 (mF ℝ z)
    rw [hFA, hJv] at e1
    obtain ⟨u⟩ := hne
    have := congrFun e1 u
    simpa [n] using this
  have hA : A.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact H.isSymm_adjMatrix
  -- eigenvalues are d or roots of F
  have heig : ∀ i, (hA.eigenvalues i - d) * (mF ℝ z).eval (hA.eigenvalues i) = 0 := by
    intro i
    set v : W → ℝ := ⇑(hA.eigenvectorBasis i)
    have hv : A *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
    have hv0 : v ≠ 0 := by
      intro h0
      have := (hA.eigenvectorBasis.orthonormal.ne_zero i)
      apply this
      ext u; exact congrFun h0 u
    have e := aeval_mulVec A v _ hv ((X - C (d : ℝ)) * mF ℝ z)
    rw [map_mul, ← mulVec_mulVec, hFA, hJv, mulVec_smul, aeval_mulVec A _ _ h1] at e
    simp only [eval_sub, eval_X, eval_C, sub_self, zero_smul, smul_zero, eval_mul] at e
    rcases smul_eq_zero.mp e.symm with h | h
    · exact h
    · exact absurd h hv0
  -- traces
  have htrA : ∑ i, hA.eigenvalues i = 0 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [SimpleGraph.trace_adjMatrix] at this; simpa using this.symm
  have htrF : ∑ i, (mF ℝ z).eval (hA.eigenvalues i) = n := by
    rw [← trace_aeval hA, hFA]; simp [J, trace, n]
  -- rational characteristic polynomial
  set P : ℚ[X] := (H.adjMatrix ℚ).charpoly with hP
  have hPmap : P.map (algebraMap ℚ ℝ) = A.charpoly := by
    rw [hP, ← charpoly_map]; congr 1; ext u v; simp [A, SimpleGraph.adjMatrix_apply]
  have hPne : P ≠ 0 := (charpoly_monic _).ne_zero
  obtain ⟨G, hPG, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hPne (d : ℚ)
  set a := rootMultiplicity (d : ℚ) P with ha
  have hPmon : P.Monic := charpoly_monic _
  rw [hPG] at hPmon
  have hGmon : G.Monic := ((monic_X_sub_C _).pow a).of_mul_monic_left hPmon
  have hsplitA : A.charpoly.Splits := hA.splits_charpoly
  have hAne : A.charpoly ≠ 0 := (charpoly_monic _).ne_zero
  have hGdvd : G.map (algebraMap ℚ ℝ) ∣ A.charpoly := by
    rw [← hPmap, hPG]; exact Polynomial.map_dvd _ (dvd_mul_left _ _)
  have hzq : (((d : ℤ) - 1 : ℤ) : ℚ) = (d : ℚ) - 1 := by push_cast; ring
  have hirr := mF_irreducible ((d : ℤ) - 1) (by omega)
  rw [hzq] at hirr
  have hzmap : (algebraMap ℚ ℝ) ((d : ℚ) - 1) = z := by simp [z]
  obtain ⟨m, hGm⟩ := eq_pow_of_roots (mF ℚ ((d : ℚ) - 1)) hirr (mF_monic ℚ _) _ G rfl hGmon
    (hsplitA.of_dvd hAne hGdvd) (by
      intro θ hθ
      have hθA : θ ∈ A.charpoly.roots :=
        Multiset.mem_of_le (Polynomial.roots.le_of_dvd hAne hGdvd) hθ
      rw [hA.roots_charpoly_eq_eigenvalues] at hθA
      obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hθA
      have hθi : θ = hA.eigenvalues i := by rw [← hi]; rfl
      have hne' : hA.eigenvalues i ≠ d := by
        intro hcontra
        apply hndvd
        rw [dvd_iff_isRoot]
        have hm : (G.map (algebraMap ℚ ℝ)).IsRoot ((algebraMap ℚ ℝ) (d : ℚ)) := by
          have h0 := (mem_roots ((hGmon.map (algebraMap ℚ ℝ)).ne_zero)).mp hθ
          rw [hθi, hcontra] at h0; simpa using h0
        rw [IsRoot, eval_map, eval₂_hom] at hm
        simpa using hm
      have hFi : (mF ℝ z).eval (hA.eigenvalues i) = 0 :=
        (mul_eq_zero.mp (heig i)).resolve_left (sub_ne_zero.mpr hne')
      rw [aeval_def, eval₂_eq_eval_map, mF_map, hzmap, hθi]; exact hFi)
  have hFmon : (mF ℝ z).Monic := mF_monic ℝ z
  have hchar : A.charpoly = (X - C (d : ℝ)) ^ a * (mF ℝ z) ^ m := by
    rw [← hPmap, hPG, hGm, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, mF_map, hzmap]
    simp
  have hroots : Multiset.map hA.eigenvalues Finset.univ.val = a • {(d : ℝ)} + m • (mF ℝ z).roots := by
    have := hA.roots_charpoly_eq_eigenvalues
    rw [hchar, roots_mul, roots_pow, roots_pow, roots_X_sub_C] at this
    · simpa using this.symm
    · exact (((monic_X_sub_C _).pow a).mul (hFmon.pow m)).ne_zero
  have hsum : ∀ f : ℝ → ℝ, ∑ i, f (hA.eigenvalues i) =
      a * f d + m * ((mF ℝ z).roots.map f).sum := by
    intro f
    rw [Finset.sum_eq_multiset_sum, show (fun i => f (hA.eigenvalues i)) = f ∘ hA.eigenvalues from rfl,
      ← Multiset.map_map, hroots, Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
      Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.sum_nsmul]
    simp [nsmul_eq_mul]
  have hcardR := hsum (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Multiset.map_const',
    Multiset.sum_replicate] at hcardR
  have hFsum := hsum (fun x => (mF ℝ z).eval x)
  have hzero : ((mF ℝ z).roots.map (fun x => (mF ℝ z).eval x)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro y hy
    obtain ⟨θ, hθ, rfl⟩ := Multiset.mem_map.mp hy
    exact isRoot_of_mem_roots hθ
  rw [hzero, mul_zero, add_zero, htrF, ← hnF] at hFsum
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have ha1 : (a : ℝ) = 1 := by
    have : (n : ℝ) * (1 - a) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  rw [mF_eval] at hnF
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm0] at hcardR
    simp only [CharP.cast_eq_zero, zero_mul, add_zero, ha1] at hcardR
    rw [hcardR] at hnF
    simp only [z] at hnF
    nlinarith
  · have hFdvd : mF ℝ z ∣ A.charpoly := by
      rw [hchar]; exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    have hFsp : (mF ℝ z).Splits := hsplitA.of_dvd hAne hFdvd
    have hc3 : (mF ℝ z).roots.card = 3 := by
      rw [(splits_iff_card_roots).mp hFsp, mF_natDegree]
    have hs1 : (mF ℝ z).roots.sum = -1 := by
      have := hFsp.nextCoeff_eq_neg_sum_roots_of_monic hFmon
      rw [mF_nextCoeff] at this; linarith
    have hid := hsum (fun x => x)
    rw [Multiset.map_id', hs1, htrA, ha1] at hid
    rw [hc3, ha1] at hcardR
    simp only [z] at hnF
    have hmd : (m : ℝ) = d := by linarith
    rw [hmd] at hcardR
    push_cast at hcardR
    nlinarith

end RgMoore3

theorem regular_graph_moore_cubic_eq_ones_degree_le_two (d : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hne : Nonempty W) (hreg : H.IsRegularOfDegree d)
    (hC : ((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2 - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ
        - ((d : ℤ) - 1) • (1 : Matrix W W ℤ) : Matrix W W ℤ) = Matrix.of (fun _ _ => (1 : ℤ))) :
    d ≤ 2 := by
  exact RgMoore3.moore_cubic d W H hne hreg hC
