import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonPiOrd
import AFTD.Kb.Tcs.ComparisonEvalMatrix
import AFTD.Kb.Tcs.ComparisonPhi1
import AFTD.Kb.Tcs.ComparisonPhi2
import AFTD.Kb.Tcs.ComparisonTriangleGram
import AFTD.Kb.Tcs.ComparisonFeature2
import AFTD.Kb.Tcs.ComparisonTriangleMatrix
import AFTD.Kb.Tcs.ComparisonFeature1
import AFTD.Kb.Tcs.ComparisonPhi1LinearIndependent
import AFTD.Kb.Tcs.ComparisonTriangleKappa
import AFTD.Kb.Tcs.ComparisonEvalKerLeSpanKappa
import AFTD.Kb.Tcs.ComparisonEdge
import AFTD.Kb.Tcs.ComparisonTriangle
import AFTD.Kb.Tcs.ComparisonPiOrdMulVecPhi2
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.ComparisonTriangleKappaMemEvalKer
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# quadratic_comparison_evaluation_kernel_and_projector

Topic: quantum   Node: cc2348dceeb5

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, Lemma 1 (Quadratic evaluation kernel). Strict orders are modelled as permutations (ranks); 'orthogonal projector onto the evaluated quotient' is stated as: symmetric, idempotent, with kernel equal to the evaluation kernel.

Let n >= 3, N = C(n,2), nu_triangle = C(n,3). Strict orders on [n] are given by permutations x of Fin n (x i = rank of label i); for an edge {a,b}, a<b, d_ab(x) = +1 if x_a < x_b and -1 otherwise. In the formal feature spaces F_1 = span{1, d_e} and F_2 = span{1, d_e, d_e d_f : e, f distinct edges} with orthonormal coordinate bases, let phi_1(x), phi_2(x) be the evaluation vectors, kappa_abc = e_(ab,ac) - e_(ab,bc) + e_(ac,bc) - e_0 the triangle relation vector of a < b < c, U_triangle the matrix with columns kappa_abc, v_triangle = U_triangle 1, and Pi_ord = I - (1/3) U_triangle U_triangle^T + v_triangle v_triangle^T / (3 (nu_triangle + 3)). Then: (1) the features 1, d_e of F_1 are linearly independent as real functions on strict orders; (2) the evaluation kernel of F_2 (coefficient vectors c with <phi_2(x), c> = 0 for every strict order x) is the span of the kappa_abc; (3) the kappa_abc are linearly independent; (4) Pi_ord is the orthogonal projector onto the evaluated quotient, i.e. Pi_ord^2 = Pi_ord, Pi_ord^T = Pi_ord, and the kernel of Pi_ord equals the evaluation kernel; (5) the image of Pi_ord has dimension 1 + N + C(N,2) - nu_triangle; (6) Pi_ord phi_2(x) = phi_2(x) for every strict order x.
-/

theorem cmpf_card_edge (n : ℕ) : Fintype.card (comparison_edge n) = n.choose 2 := by
  classical
  have hc := Fintype.card_finset_len (α := Fin n) 2
  rw [Fintype.card_fin] at hc
  rw [← hc]
  refine Fintype.card_congr (Equiv.ofBijective
    (fun e : comparison_edge n => (⟨{e.1.1, e.1.2}, Finset.card_pair (ne_of_lt e.2)⟩ :
      {s : Finset (Fin n) // s.card = 2})) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
    have hab2 : a.val < b.val := hab
    have hab2' : a'.val < b'.val := hab'
    simp only [Subtype.mk.injEq] at h
    have h1 : a ∈ ({a', b'} : Finset (Fin n)) := h ▸ Finset.mem_insert_self _ _
    have h2 : b ∈ ({a', b'} : Finset (Fin n)) := h ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h1 h2
    simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff]
    omega
  · rintro ⟨s, hs⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨⟨(x, y), h⟩, rfl⟩
    · exact ⟨⟨(y, x), h⟩, by simp only [Subtype.mk.injEq]; exact Finset.pair_comm _ _⟩

theorem cmpf_card_triangle (n : ℕ) : Fintype.card (comparison_triangle n) = n.choose 3 := by
  classical
  have hc := Fintype.card_finset_len (α := Fin n) 3
  rw [Fintype.card_fin] at hc
  rw [← hc]
  refine Fintype.card_congr (Equiv.ofBijective
    (fun t : comparison_triangle n => (⟨{t.1.1, t.1.2.1, t.1.2.2}, by
      rw [Finset.card_eq_three]
      exact ⟨_, _, _, ne_of_lt t.2.1, ne_of_lt (t.2.1.trans t.2.2), ne_of_lt t.2.2, rfl⟩⟩ :
      {s : Finset (Fin n) // s.card = 3})) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, b, c⟩, hab, hbc⟩ ⟨⟨a', b', c'⟩, hab', hbc'⟩ h
    simp only [Fin.lt_def] at hab hbc hab' hbc'
    simp only [Subtype.mk.injEq] at h
    have m : ∀ v, v ∈ ({a, b, c} : Finset (Fin n)) ↔ v ∈ ({a', b', c'} : Finset (Fin n)) :=
      fun v => by rw [h]
    have h1 := (m a).mp (by simp)
    have h2 := (m b).mp (by simp)
    have h3 := (m c).mp (by simp)
    have h4 := (m a').mpr (by simp)
    have h5 := (m b').mpr (by simp)
    have h6 := (m c').mpr (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h1 h2 h3 h4 h5 h6
    simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff]
    omega
  · rintro ⟨s, hs⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hs
    rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
      rcases lt_or_gt_of_ne hyz with h3 | h3
    · exact ⟨⟨(x, y, z), h1, h3⟩, by simp only [Subtype.mk.injEq]⟩
    · exact ⟨⟨(x, z, y), h2, h3⟩, by simp only [Subtype.mk.injEq]; ext; simp; tauto⟩
    · exact absurd (h1.trans h3) (not_lt.mpr h2.le)
    · exact ⟨⟨(z, x, y), h2, h1⟩, by simp only [Subtype.mk.injEq]; ext; simp; tauto⟩
    · exact ⟨⟨(y, x, z), h1, h2⟩, by simp only [Subtype.mk.injEq]; ext; simp; tauto⟩
    · exact absurd (h3.trans h1) (not_lt.mpr h2.le)
    · exact ⟨⟨(y, z, x), h3, h2⟩, by simp only [Subtype.mk.injEq]; ext; simp; tauto⟩
    · exact ⟨⟨(z, y, x), h3, h1⟩, by simp only [Subtype.mk.injEq]; ext; simp; tauto⟩

theorem quadratic_comparison_evaluation_kernel_and_projector (n : ℕ) (hn : 3 ≤ n) :
    LinearIndependent ℝ
        (fun i : comparison_feature1 n => fun x : Equiv.Perm (Fin n) => comparison_phi1 x i) ∧
      LinearMap.ker (comparison_eval_matrix n).mulVecLin =
        Submodule.span ℝ (Set.range (comparison_triangle_kappa (n := n))) ∧
      LinearIndependent ℝ (comparison_triangle_kappa (n := n)) ∧
      comparison_pi_ord n * comparison_pi_ord n = comparison_pi_ord n ∧
      (comparison_pi_ord n).transpose = comparison_pi_ord n ∧
      LinearMap.ker (comparison_pi_ord n).mulVecLin =
        LinearMap.ker (comparison_eval_matrix n).mulVecLin ∧
      Module.finrank ℝ (LinearMap.range (comparison_pi_ord n).mulVecLin) =
        1 + n.choose 2 + (n.choose 2).choose 2 - n.choose 3 ∧
      ∀ x : Equiv.Perm (Fin n),
        Matrix.mulVec (comparison_pi_ord n) (comparison_phi2 x) = comparison_phi2 x := by
  classical
  set U := comparison_triangle_matrix n with hU
  have hG := comparison_triangle_gram n
  rw [← hU] at hG
  have hν := cmpf_card_triangle n
  have hN := cmpf_card_edge n
  have hUt : U.transpose = fun t => comparison_triangle_kappa t := by
    funext t i; rfl
  have hrangeU : LinearMap.range U.mulVecLin =
      Submodule.span ℝ (Set.range (comparison_triangle_kappa (n := n))) := by
    rw [Matrix.range_mulVecLin]
    rfl
  have hker : LinearMap.ker (comparison_eval_matrix n).mulVecLin =
      Submodule.span ℝ (Set.range (comparison_triangle_kappa (n := n))) := by
    refine le_antisymm (comparison_eval_ker_le_span_kappa n) (Submodule.span_le.mpr ?_)
    rintro _ ⟨t, rfl⟩
    exact LinearMap.mem_ker.mpr (by
      rw [Matrix.mulVecLin_apply]; exact comparison_triangle_kappa_mem_eval_ker n t)
  set ν : ℝ := (n.choose 3 : ℝ) with hνdef
  set J : Matrix (comparison_triangle n) (comparison_triangle n) ℝ :=
    Matrix.of fun _ _ => (1 : ℝ) with hJ
  set κc : ℝ := 1 / (3 * (ν + 3)) with hκc
  set B : Matrix (comparison_triangle n) (comparison_triangle n) ℝ :=
    (1 / 3 : ℝ) • (1 : Matrix (comparison_triangle n) (comparison_triangle n) ℝ) - κc • J
    with hB
  have hJJ : J * J = ν • J := by
    ext i j
    simp [J, Matrix.mul_apply, hν, ν]
  have hν0 : (0 : ℝ) ≤ ν := by positivity
  have hscal : (1 / 3 : ℝ) - κc * 3 - κc * ν = 0 := by
    rw [hκc]; field_simp; ring
  have hBM : B * (U.transpose * U) = 1 := by
    rw [hG, hB, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, hJJ]
    simp only [smul_smul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, J,
      Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> linarith [hscal]
  have hBt : B.transpose = B := by
    rw [hB, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul,
      Matrix.transpose_one]
    congr 2
  have hPi : comparison_pi_ord n = 1 - U * B * U.transpose := by
    have hv : Matrix.vecMulVec (U.mulVec (fun _ => 1)) (U.mulVec (fun _ => 1)) =
        U * J * U.transpose := by
      ext i j
      simp only [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, mul_one, Matrix.mul_apply,
        J, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    unfold comparison_pi_ord
    dsimp only
    rw [← hU, hv, hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hκc, hνdef]
    abel
  have hUBU : U * B * U.transpose * U = U := by
    simp only [Matrix.mul_assoc]
    rw [hBM, Matrix.mul_one]
  clear_value B J κc ν
  have hP2 : comparison_pi_ord n * comparison_pi_ord n = comparison_pi_ord n := by
    rw [hPi, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one]
    have : U * B * U.transpose * (U * B * U.transpose) = U * B * U.transpose := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUBU]
    rw [this]
    abel
  have hPt : (comparison_pi_ord n).transpose = comparison_pi_ord n := by
    rw [hPi, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, hBt, Matrix.mul_assoc]
  have hLI : LinearIndependent ℝ (comparison_triangle_kappa (n := n)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hUg : U.mulVec g = 0 := by
      rw [← hg]
      funext i
      simp [Matrix.mulVec, dotProduct, U, comparison_triangle_matrix, mul_comm, Finset.sum_apply]
    have : g = (B * (U.transpose * U)).mulVec g := by rw [hBM, Matrix.one_mulVec]
    intro t
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUg, Matrix.mulVec_zero,
      Matrix.mulVec_zero]
    rfl
  have hkerP : LinearMap.ker (comparison_pi_ord n).mulVecLin = LinearMap.range U.mulVecLin := by
    ext c
    simp only [LinearMap.mem_ker, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · intro h
      refine ⟨(B * U.transpose).mulVec c, ?_⟩
      rw [hPi, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
      exact h.symm
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, hPi, Matrix.sub_mul, Matrix.one_mul, hUBU, sub_self,
        Matrix.zero_mulVec]
  have hfr : Module.finrank ℝ (LinearMap.ker (comparison_pi_ord n).mulVecLin) = n.choose 3 := by
    rw [hkerP, hrangeU, finrank_span_eq_card hLI, hν]
  refine ⟨comparison_phi1_linearIndependent n, hker, hLI, hP2, hPt, ?_, ?_,
    fun x => comparison_pi_ord_mulVec_phi2 n x⟩
  · rw [hkerP, hrangeU, hker]
  · have hrn := LinearMap.finrank_range_add_finrank_ker (comparison_pi_ord n).mulVecLin
    rw [hfr, Module.finrank_fintype_fun_eq_card] at hrn
    have hcard : Fintype.card (comparison_feature2 n) =
        1 + n.choose 2 + (n.choose 2).choose 2 := by
      rw [Fintype.card_sum, Fintype.card_option, Fintype.card_finset_len, hN]
      ring
    omega
