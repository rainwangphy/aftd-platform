import AFTD.Prelude
import AFTD.Kb.Tcs.PauliLiouvilleMomentTwo
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.PauliOp
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.InstFintypePauliString
import AFTD.Kb.Tcs.RCLikeNormSqEqConjMulSelf
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.PauliMatrix
import AFTD.Kb.Tcs.PauliPhase
import AFTD.Kb.Tcs.PauliBasisToMatrix
import AFTD.Kb.Tcs.SigmaI
import AFTD.Kb.Tcs.SigmaX
import AFTD.Kb.Tcs.SigmaY
import AFTD.Kb.Tcs.SigmaZ

/-!
# pauli_moment_two_eq_four_replica_sum

Topic: quantum_mechanics   Node: a7e03dd12822

Provenance: helper lemma. step towards op_1695_magic_sixteen_spin_identity

For every natural number n and n-qubit pure state ψ in Hn n, the second Pauli-Liouville moment (pauliLiouvilleMomentTwo n ψ as a complex number) equals the 4-replica correlation sum over bit-flip shift a and replica bitstrings x1, x2, x3 in Fin n → Fin 2, where x4 = x1 + x2 + x3.
-/

open scoped BigOperators Classical

private def pauli_moment_two_eq_four_replica_sum_xs : PauliBasis → Fin 2 :=
  fun q => if q = PauliBasis.X ∨ q = PauliBasis.Y then 1 else 0

private def pauli_moment_two_eq_four_replica_sum_zs : PauliBasis → Fin 2 :=
  fun q => if q = PauliBasis.Y ∨ q = PauliBasis.Z then 1 else 0

private def pauli_moment_two_eq_four_replica_sum_mk (x z : Fin 2) : PauliBasis :=
  if x = 0 then (if z = 0 then PauliBasis.I else PauliBasis.Z)
  else (if z = 0 then PauliBasis.X else PauliBasis.Y)

private def pauli_moment_two_eq_four_replica_sum_chi (n : ℕ) (b s : Fin n → Fin 2) : ℂ :=
  ∏ k, (-1 : ℂ) ^ ((b k).val * (s k).val)

private def pauli_moment_two_eq_four_replica_sum_c (n : ℕ) (ψ : Hn n) (a i : Fin n → Fin 2) : ℂ :=
  starRingEnd ℂ (ψ i) * ψ (i + a)

private def pauli_moment_two_eq_four_replica_sum_W (n : ℕ) (ψ : Hn n) (a b : Fin n → Fin 2) : ℂ :=
  ∑ i, pauli_moment_two_eq_four_replica_sum_c n ψ a i * pauli_moment_two_eq_four_replica_sum_chi n b i

private def pauli_moment_two_eq_four_replica_sum_S (n : ℕ) (ψ : Hn n) (a : Fin n → Fin 2) : ℂ :=
  ∑ i1 : Fin n → Fin 2, ∑ i2 : Fin n → Fin 2, ∑ i3 : Fin n → Fin 2, ∑ i4 : Fin n → Fin 2,
    if i1 + i2 + i3 + i4 = 0 then
      pauli_moment_two_eq_four_replica_sum_c n ψ a i1 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i2) *
        pauli_moment_two_eq_four_replica_sum_c n ψ a i3 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i4)
    else 0

private lemma pauli_moment_two_eq_four_replica_sum_inner_eq_sum (n : ℕ) (ψ φ : Hn n) :
    inner ℂ ψ φ = ∑ i, starRingEnd ℂ (ψ i) * φ i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private lemma pauli_moment_two_eq_four_replica_sum_pauliOp_apply (n : ℕ) (p : PauliString n) (ψ : Hn n) (i : Fin n → Fin 2) :
    (pauliOp p ψ) i = ∑ j, pauliMatrix p i j * ψ j := by
  simp [pauliOp, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

private lemma pauli_moment_two_eq_four_replica_sum_prod_ite_indicator {ι : Type*} [Fintype ι] (c : ι → Prop) [DecidablePred c] :
    (∏ i, (if c i then (1:ℂ) else 0)) = if (∀ i, c i) then 1 else 0 := by
  by_cases h : ∀ i, c i
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i _ => by rw [if_pos (h i)])
  · rw [if_neg h]
    simp only [not_forall] at h
    obtain ⟨i0, hi0⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i0) (by rw [if_neg hi0])

private lemma pauli_moment_two_eq_four_replica_sum_prod_three {ι : Type*} [Fintype ι] (A B C : ι → ℂ) :
    (∏ k, A k * B k * C k) = (∏ k, A k) * (∏ k, B k) * (∏ k, C k) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

private lemma pauli_moment_two_eq_four_replica_sum_entry_coord (q : PauliBasis) (x y : Fin 2) :
    q.toMatrix x y = pauliPhase q * (if y = x + pauli_moment_two_eq_four_replica_sum_xs q then 1 else 0) *
      (-1 : ℂ) ^ ((pauli_moment_two_eq_four_replica_sum_zs q).val * x.val) := by
  cases q <;> fin_cases x <;> fin_cases y <;>
    simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ, pauliPhase,
      pauli_moment_two_eq_four_replica_sum_xs, pauli_moment_two_eq_four_replica_sum_zs]

private lemma pauli_moment_two_eq_four_replica_sum_matrix_entry (n : ℕ) (p : PauliString n) (i j : Fin n → Fin 2) :
    pauliMatrix p i j = (∏ k, pauliPhase (p k)) *
      (if j = i + (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k)) then 1 else 0) *
      (∏ k, (-1 : ℂ) ^ ((pauli_moment_two_eq_four_replica_sum_zs (p k)).val * (i k).val)) := by
  have hcoord : ∀ k, (p k).toMatrix (i k) (j k) = pauliPhase (p k) *
      (if j k = i k + pauli_moment_two_eq_four_replica_sum_xs (p k) then 1 else 0) *
      (-1 : ℂ) ^ ((pauli_moment_two_eq_four_replica_sum_zs (p k)).val * (i k).val) :=
    fun k => pauli_moment_two_eq_four_replica_sum_entry_coord (p k) (i k) (j k)
  have h1 : (∏ k, (if j k = i k + pauli_moment_two_eq_four_replica_sum_xs (p k) then (1:ℂ) else 0))
      = (if j = i + (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k)) then 1 else 0) := by
    rw [pauli_moment_two_eq_four_replica_sum_prod_ite_indicator]
    by_cases hh : (∀ k, j k = i k + pauli_moment_two_eq_four_replica_sum_xs (p k))
    · have hq : (j = i + (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k))) := by
        rw [funext_iff]; intro k; rw [Pi.add_apply]; exact hh k
      rw [if_pos hh, if_pos hq]
    · have hq : ¬ (j = i + (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k))) := by
        intro hcon
        exact hh (fun k => congrFun hcon k)
      rw [if_neg hh, if_neg hq]
  simp only [pauliMatrix, hcoord, pauli_moment_two_eq_four_replica_sum_prod_three]
  rw [h1]

private lemma pauli_moment_two_eq_four_replica_sum_inner_support (n : ℕ) (ψ : Hn n) (p : PauliString n) :
    inner ℂ ψ (pauliOp p ψ) = (∏ k, pauliPhase (p k)) *
      ∑ i : Fin n → Fin 2, starRingEnd ℂ (ψ i) * ψ (i + (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k))) *
        (∏ k, (-1 : ℂ) ^ ((pauli_moment_two_eq_four_replica_sum_zs (p k)).val * (i k).val)) := by
  have key : ∀ i : Fin n → Fin 2, (∑ j, pauliMatrix p i j * ψ j) =
      (∏ k, pauliPhase (p k)) *
        (ψ (i + (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k))) *
          (∏ k, (-1 : ℂ) ^ ((pauli_moment_two_eq_four_replica_sum_zs (p k)).val * (i k).val))) := by
    intro i
    simp only [pauli_moment_two_eq_four_replica_sum_matrix_entry]
    have hstep : ∀ j, ((∏ k, pauliPhase (p k)) *
          (if j = i + (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k)) then 1 else 0) *
          (∏ k, (-1 : ℂ) ^ ((pauli_moment_two_eq_four_replica_sum_zs (p k)).val * (i k).val))) * ψ j
        = ((∏ k, pauliPhase (p k)) *
          (∏ k, (-1 : ℂ) ^ ((pauli_moment_two_eq_four_replica_sum_zs (p k)).val * (i k).val))) *
          ((if j = i + (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k)) then 1 else 0) * ψ j) := by
      intro j; ring
    simp only [hstep, ← Finset.mul_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  simp only [pauli_moment_two_eq_four_replica_sum_inner_eq_sum, pauli_moment_two_eq_four_replica_sum_pauliOp_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [key i]
  ring

private lemma pauli_moment_two_eq_four_replica_sum_norm_four (z : ℂ) :
    ((‖z‖ ^ 4 : ℝ) : ℂ) = z ^ 2 * (starRingEnd ℂ z) ^ 2 := by
  have h : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  have h2 : ((‖z‖ ^ 4 : ℝ) : ℂ) = ((Complex.normSq z : ℂ)) ^ 2 := by
    rw [h]; push_cast; ring
  rw [h2, Complex.normSq_eq_conj_mul_self]
  ring

private lemma pauli_moment_two_eq_four_replica_sum_norm_four' (z : ℂ) :
    ((‖z‖ : ℂ)) ^ 4 = z ^ 2 * (starRingEnd ℂ z) ^ 2 := by
  rw [← Complex.ofReal_pow]
  exact pauli_moment_two_eq_four_replica_sum_norm_four z

private lemma pauli_moment_two_eq_four_replica_sum_neg_one_pow_add (c a b : Fin 2) :
    (-1 : ℂ) ^ (c.val * (a + b).val) = (-1) ^ (c.val * a.val) * (-1) ^ (c.val * b.val) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

private lemma pauli_moment_two_eq_four_replica_sum_chi_mul (n : ℕ) (b s t : Fin n → Fin 2) :
    pauli_moment_two_eq_four_replica_sum_chi n b (s + t)
      = pauli_moment_two_eq_four_replica_sum_chi n b s * pauli_moment_two_eq_four_replica_sum_chi n b t := by
  simp only [pauli_moment_two_eq_four_replica_sum_chi]
  rw [Finset.prod_congr rfl (fun k (_ : k ∈ Finset.univ) => by
    rw [Pi.add_apply, pauli_moment_two_eq_four_replica_sum_neg_one_pow_add]), Finset.prod_mul_distrib]

private lemma pauli_moment_two_eq_four_replica_sum_chi_conj (n : ℕ) (b s : Fin n → Fin 2) :
    starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_chi n b s) = pauli_moment_two_eq_four_replica_sum_chi n b s := by
  rw [pauli_moment_two_eq_four_replica_sum_chi, map_prod]
  exact Finset.prod_congr rfl (fun k _ => by rw [map_pow]; norm_num)

private lemma pauli_moment_two_eq_four_replica_sum_sum_chi_coord (v : Fin 2) :
    (∑ c : Fin 2, (-1 : ℂ) ^ (c.val * v.val)) = if v = 0 then 2 else 0 := by
  fin_cases v <;> simp

private lemma pauli_moment_two_eq_four_replica_sum_prod_sum_swap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] (f : ∀ i, β i → ℂ) :
    (∏ i, ∑ y, f i y) = ∑ x : ∀ i, β i, ∏ i, f i (x i) := by
  rw [Finset.prod_univ_sum]
  simp

private lemma pauli_moment_two_eq_four_replica_sum_chi_sum (n : ℕ) (s : Fin n → Fin 2) :
    (∑ b : Fin n → Fin 2, pauli_moment_two_eq_four_replica_sum_chi n b s) = (2:ℂ)^n * (if s = 0 then 1 else 0) := by
  have hswap : (∏ k, (∑ c : Fin 2, (-1:ℂ)^(c.val * (s k).val)))
      = ∑ b : Fin n → Fin 2, pauli_moment_two_eq_four_replica_sum_chi n b s := by
    rw [pauli_moment_two_eq_four_replica_sum_prod_sum_swap (fun _ => Fin 2) (fun k c => (-1:ℂ)^(c.val * (s k).val))]
    exact Finset.sum_congr rfl (fun b _ => by simp only [pauli_moment_two_eq_four_replica_sum_chi])
  rw [← hswap]
  simp only [pauli_moment_two_eq_four_replica_sum_sum_chi_coord]
  by_cases h : s = 0
  · have hall : ∀ k, s k = 0 := fun k => congrFun h k
    rw [if_pos h, Finset.prod_congr rfl (fun k _ => if_pos (hall k))]
    simp
  · rw [if_neg h]
    have hne : ∃ k, s k ≠ 0 := by
      by_contra hc
      apply h
      funext k
      by_contra hk
      exact hc ⟨k, hk⟩
    obtain ⟨k0, hk0⟩ := hne
    rw [Finset.prod_eq_zero (Finset.mem_univ k0) (if_neg hk0)]
    simp

private lemma pauli_moment_two_eq_four_replica_sum_pauliPhase_conj (q : PauliBasis) :
    pauliPhase q * starRingEnd ℂ (pauliPhase q) = 1 := by
  cases q <;> simp [pauliPhase]

private lemma pauli_moment_two_eq_four_replica_sum_phase_conj (n : ℕ) (p : PauliString n) :
    (∏ k, pauliPhase (p k)) * starRingEnd ℂ (∏ k, pauliPhase (p k)) = 1 := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun k _ => pauli_moment_two_eq_four_replica_sum_pauliPhase_conj (p k))

private lemma pauli_moment_two_eq_four_replica_sum_moment_eq (n : ℕ) (ψ : Hn n) :
    (pauliLiouvilleMomentTwo n ψ : ℂ) = (1 / (2:ℂ)^n) * ∑ p : PauliString n,
      (inner ℂ ψ (pauliOp p ψ))^2 * (starRingEnd ℂ (inner ℂ ψ (pauliOp p ψ)))^2 := by
  rw [pauliLiouvilleMomentTwo]
  push_cast
  congr 1
  exact Finset.sum_congr rfl (fun p _ => pauli_moment_two_eq_four_replica_sum_norm_four' (inner ℂ ψ (pauliOp p ψ)))

private lemma pauli_moment_two_eq_four_replica_sum_four_prod (n : ℕ) (b i1 i2 i3 i4 : Fin n → Fin 2) :
    pauli_moment_two_eq_four_replica_sum_chi n b i1 * pauli_moment_two_eq_four_replica_sum_chi n b i2 *
        pauli_moment_two_eq_four_replica_sum_chi n b i3 * pauli_moment_two_eq_four_replica_sum_chi n b i4
      = pauli_moment_two_eq_four_replica_sum_chi n b (i1 + i2 + i3 + i4) := by
  rw [← pauli_moment_two_eq_four_replica_sum_chi_mul, ← pauli_moment_two_eq_four_replica_sum_chi_mul,
    ← pauli_moment_two_eq_four_replica_sum_chi_mul]

private lemma pauli_moment_two_eq_four_replica_sum_conj_W (n : ℕ) (ψ : Hn n) (a b : Fin n → Fin 2) :
    starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_W n ψ a b)
      = ∑ i, starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i) * pauli_moment_two_eq_four_replica_sum_chi n b i := by
  simp only [pauli_moment_two_eq_four_replica_sum_W, map_sum, map_mul, pauli_moment_two_eq_four_replica_sum_chi_conj]

private lemma pauli_moment_two_eq_four_replica_sum_inner_eq_W (n : ℕ) (ψ : Hn n) (p : PauliString n) :
    inner ℂ ψ (pauliOp p ψ) = (∏ k, pauliPhase (p k)) *
      pauli_moment_two_eq_four_replica_sum_W n ψ (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k))
        (fun k => pauli_moment_two_eq_four_replica_sum_zs (p k)) := by
  rw [pauli_moment_two_eq_four_replica_sum_inner_support]
  simp only [pauli_moment_two_eq_four_replica_sum_W, pauli_moment_two_eq_four_replica_sum_c,
    pauli_moment_two_eq_four_replica_sum_chi]

private lemma pauli_moment_two_eq_four_replica_sum_aux (P W : ℂ) (h : P * starRingEnd ℂ P = 1) :
    (P * W)^2 * (starRingEnd ℂ P * starRingEnd ℂ W)^2 = W^2 * (starRingEnd ℂ W)^2 := by
  have h2 : (P * starRingEnd ℂ P)^2 = 1 := by rw [h]; ring
  calc (P * W)^2 * (starRingEnd ℂ P * starRingEnd ℂ W)^2
      = (P * starRingEnd ℂ P)^2 * (W^2 * (starRingEnd ℂ W)^2) := by ring
    _ = W^2 * (starRingEnd ℂ W)^2 := by rw [h2]; ring

private lemma pauli_moment_two_eq_four_replica_sum_zsq_conjsq (n : ℕ) (ψ : Hn n) (p : PauliString n) :
    (inner ℂ ψ (pauliOp p ψ))^2 * (starRingEnd ℂ (inner ℂ ψ (pauliOp p ψ)))^2
    = (pauli_moment_two_eq_four_replica_sum_W n ψ (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k))
          (fun k => pauli_moment_two_eq_four_replica_sum_zs (p k)))^2 *
      (starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_W n ψ (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k))
          (fun k => pauli_moment_two_eq_four_replica_sum_zs (p k))))^2 := by
  rw [pauli_moment_two_eq_four_replica_sum_inner_eq_W, map_mul]
  exact pauli_moment_two_eq_four_replica_sum_aux _ _ (pauli_moment_two_eq_four_replica_sum_phase_conj n p)

private lemma pauli_moment_two_eq_four_replica_sum_term (n : ℕ) (ψ : Hn n) (a b i1 i2 i3 i4 : Fin n → Fin 2) :
    ((pauli_moment_two_eq_four_replica_sum_c n ψ a i1 * pauli_moment_two_eq_four_replica_sum_chi n b i1) *
        (pauli_moment_two_eq_four_replica_sum_c n ψ a i3 * pauli_moment_two_eq_four_replica_sum_chi n b i3)) *
      ((starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i2) * pauli_moment_two_eq_four_replica_sum_chi n b i2) *
        (starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i4) * pauli_moment_two_eq_four_replica_sum_chi n b i4))
    = pauli_moment_two_eq_four_replica_sum_c n ψ a i1 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i2) *
        pauli_moment_two_eq_four_replica_sum_c n ψ a i3 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i4) *
        pauli_moment_two_eq_four_replica_sum_chi n b (i1 + i2 + i3 + i4) := by
  have hchi := pauli_moment_two_eq_four_replica_sum_four_prod n b i1 i2 i3 i4
  calc ((pauli_moment_two_eq_four_replica_sum_c n ψ a i1 * pauli_moment_two_eq_four_replica_sum_chi n b i1) *
        (pauli_moment_two_eq_four_replica_sum_c n ψ a i3 * pauli_moment_two_eq_four_replica_sum_chi n b i3)) *
        ((starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i2) * pauli_moment_two_eq_four_replica_sum_chi n b i2) *
          (starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i4) * pauli_moment_two_eq_four_replica_sum_chi n b i4))
      = (pauli_moment_two_eq_four_replica_sum_c n ψ a i1 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i2) *
          pauli_moment_two_eq_four_replica_sum_c n ψ a i3 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i4)) *
        (pauli_moment_two_eq_four_replica_sum_chi n b i1 * pauli_moment_two_eq_four_replica_sum_chi n b i2 *
          pauli_moment_two_eq_four_replica_sum_chi n b i3 * pauli_moment_two_eq_four_replica_sum_chi n b i4) := by ring
    _ = _ := by rw [hchi]

private lemma pauli_moment_two_eq_four_replica_sum_expand (n : ℕ) (ψ : Hn n) (a b : Fin n → Fin 2) :
    (pauli_moment_two_eq_four_replica_sum_W n ψ a b)^2 *
        (starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_W n ψ a b))^2 =
      ∑ i1 : Fin n → Fin 2, ∑ i2 : Fin n → Fin 2, ∑ i3 : Fin n → Fin 2, ∑ i4 : Fin n → Fin 2,
        pauli_moment_two_eq_four_replica_sum_c n ψ a i1 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i2) *
          pauli_moment_two_eq_four_replica_sum_c n ψ a i3 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i4) *
          pauli_moment_two_eq_four_replica_sum_chi n b (i1 + i2 + i3 + i4) := by
  simp only [pow_two]
  rw [pauli_moment_two_eq_four_replica_sum_conj_W, pauli_moment_two_eq_four_replica_sum_W]
  set f : (Fin n → Fin 2) → ℂ := fun i => pauli_moment_two_eq_four_replica_sum_c n ψ a i * pauli_moment_two_eq_four_replica_sum_chi n b i with hf
  set g : (Fin n → Fin 2) → ℂ := fun i => starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i) * pauli_moment_two_eq_four_replica_sum_chi n b i with hg
  have hF : (∑ i, f i) * (∑ i, f i) = ∑ i1, ∑ i3, f i1 * f i3 := by
    simpa using (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ) (f := f) (g := f))
  have hG : (∑ i, g i) * (∑ i, g i) = ∑ i2, ∑ i4, g i2 * g i4 := by
    simpa using (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ) (f := g) (g := g))
  have hstep : (∑ i1, ∑ i3, f i1 * f i3) * (∑ i2, ∑ i4, g i2 * g i4)
      = ∑ i1, ∑ i2, (∑ i3, f i1 * f i3) * (∑ i4, g i2 * g i4) := by
    simpa using (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
      (f := fun i1 => ∑ i3, f i1 * f i3) (g := fun i2 => ∑ i4, g i2 * g i4))
  have hstep2 : ∀ i1 i2 : Fin n → Fin 2,
      (∑ i3, f i1 * f i3) * (∑ i4, g i2 * g i4) = ∑ i3, ∑ i4, (f i1 * f i3) * (g i2 * g i4) := by
    intro i1 i2
    simpa using (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
      (f := fun i3 => f i1 * f i3) (g := fun i4 => g i2 * g i4))
  rw [hF, hG, hstep]
  simp only [hstep2]
  refine Finset.sum_congr rfl (fun i1 _ => Finset.sum_congr rfl (fun i2 _ =>
    Finset.sum_congr rfl (fun i3 _ => Finset.sum_congr rfl (fun i4 _ => ?_))))
  rw [hf, hg]
  exact pauli_moment_two_eq_four_replica_sum_term n ψ a b i1 i2 i3 i4

private lemma pauli_moment_two_eq_four_replica_sum_xs_mk (x z : Fin 2) :
    pauli_moment_two_eq_four_replica_sum_xs (pauli_moment_two_eq_four_replica_sum_mk x z) = x := by
  fin_cases x <;> fin_cases z <;> simp [pauli_moment_two_eq_four_replica_sum_mk, pauli_moment_two_eq_four_replica_sum_xs]

private lemma pauli_moment_two_eq_four_replica_sum_zs_mk (x z : Fin 2) :
    pauli_moment_two_eq_four_replica_sum_zs (pauli_moment_two_eq_four_replica_sum_mk x z) = z := by
  fin_cases x <;> fin_cases z <;> simp [pauli_moment_two_eq_four_replica_sum_mk, pauli_moment_two_eq_four_replica_sum_zs]

private lemma pauli_moment_two_eq_four_replica_sum_mk_xs_zs (q : PauliBasis) :
    pauli_moment_two_eq_four_replica_sum_mk (pauli_moment_two_eq_four_replica_sum_xs q)
      (pauli_moment_two_eq_four_replica_sum_zs q) = q := by
  cases q <;> simp [pauli_moment_two_eq_four_replica_sum_mk, pauli_moment_two_eq_four_replica_sum_xs,
    pauli_moment_two_eq_four_replica_sum_zs]

private lemma pauli_moment_two_eq_four_replica_sum_bij (n : ℕ) :
    Function.Bijective (fun p : PauliString n =>
      ((fun k => pauli_moment_two_eq_four_replica_sum_xs (p k)), (fun k => pauli_moment_two_eq_four_replica_sum_zs (p k)))) := by
  constructor
  · intro p q h
    have h1 : (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k)) = (fun k => pauli_moment_two_eq_four_replica_sum_xs (q k)) := congrArg Prod.fst h
    have h2 : (fun k => pauli_moment_two_eq_four_replica_sum_zs (p k)) = (fun k => pauli_moment_two_eq_four_replica_sum_zs (q k)) := congrArg Prod.snd h
    funext k
    calc p k = pauli_moment_two_eq_four_replica_sum_mk (pauli_moment_two_eq_four_replica_sum_xs (p k)) (pauli_moment_two_eq_four_replica_sum_zs (p k)) := (pauli_moment_two_eq_four_replica_sum_mk_xs_zs (p k)).symm
      _ = pauli_moment_two_eq_four_replica_sum_mk (pauli_moment_two_eq_four_replica_sum_xs (q k)) (pauli_moment_two_eq_four_replica_sum_zs (q k)) := by rw [congrFun h1 k, congrFun h2 k]
      _ = q k := pauli_moment_two_eq_four_replica_sum_mk_xs_zs (q k)
  · rintro ⟨a, b⟩
    refine ⟨fun k => pauli_moment_two_eq_four_replica_sum_mk (a k) (b k), ?_⟩
    have h1 : (fun k => pauli_moment_two_eq_four_replica_sum_xs ((fun k => pauli_moment_two_eq_four_replica_sum_mk (a k) (b k)) k)) = a := by
      funext k; exact pauli_moment_two_eq_four_replica_sum_xs_mk (a k) (b k)
    have h2 : (fun k => pauli_moment_two_eq_four_replica_sum_zs ((fun k => pauli_moment_two_eq_four_replica_sum_mk (a k) (b k)) k)) = b := by
      funext k; exact pauli_moment_two_eq_four_replica_sum_zs_mk (a k) (b k)
    exact Prod.ext h1 h2

private lemma pauli_moment_two_eq_four_replica_sum_sum_bij (n : ℕ) (F : (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ) :
    (∑ p : PauliString n, F (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k)) (fun k => pauli_moment_two_eq_four_replica_sum_zs (p k)))
      = ∑ a : Fin n → Fin 2, ∑ b : Fin n → Fin 2, F a b := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_bijective _ (pauli_moment_two_eq_four_replica_sum_bij n) _ _ (fun p => rfl)

private lemma pauli_moment_two_eq_four_replica_sum_factor4 {α : Type*} [Fintype α] (c : ℂ) (Y : α → α → α → α → ℂ) :
    (∑ i1, ∑ i2, ∑ i3, ∑ i4, c * Y i1 i2 i3 i4)
      = c * ∑ i1, ∑ i2, ∑ i3, ∑ i4, Y i1 i2 i3 i4 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i1 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i2 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i3 _ => ?_)
  rw [Finset.mul_sum]

private lemma pauli_moment_two_eq_four_replica_sum_sum_b_step (n : ℕ) (ψ : Hn n) (a : Fin n → Fin 2) :
    (∑ b : Fin n → Fin 2, (pauli_moment_two_eq_four_replica_sum_W n ψ a b)^2 *
        (starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_W n ψ a b))^2)
      = (2:ℂ)^n * pauli_moment_two_eq_four_replica_sum_S n ψ a := by
  have h1 : ∀ b : Fin n → Fin 2, (pauli_moment_two_eq_four_replica_sum_W n ψ a b)^2 *
        (starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_W n ψ a b))^2
      = ∑ i1, ∑ i2, ∑ i3, ∑ i4, pauli_moment_two_eq_four_replica_sum_c n ψ a i1 *
          starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i2) *
          pauli_moment_two_eq_four_replica_sum_c n ψ a i3 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i4) *
          pauli_moment_two_eq_four_replica_sum_chi n b (i1 + i2 + i3 + i4) :=
    fun b => pauli_moment_two_eq_four_replica_sum_expand n ψ a b
  simp only [h1]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i1 (_ : i1 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun i1 (_ : i1 ∈ Finset.univ) => Finset.sum_congr rfl
    (fun i2 (_ : i2 ∈ Finset.univ) => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun i1 (_ : i1 ∈ Finset.univ) => Finset.sum_congr rfl
    (fun i2 (_ : i2 ∈ Finset.univ) => Finset.sum_congr rfl (fun i3 (_ : i3 ∈ Finset.univ) => Finset.sum_comm)))]
  have hstep2 : ∀ i1 i2 i3 i4 : Fin n → Fin 2,
      (∑ b : Fin n → Fin 2, pauli_moment_two_eq_four_replica_sum_c n ψ a i1 *
          starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i2) * pauli_moment_two_eq_four_replica_sum_c n ψ a i3 *
          starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i4) * pauli_moment_two_eq_four_replica_sum_chi n b (i1 + i2 + i3 + i4))
      = (2:ℂ)^n * (if i1 + i2 + i3 + i4 = 0 then
          pauli_moment_two_eq_four_replica_sum_c n ψ a i1 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i2) *
            pauli_moment_two_eq_four_replica_sum_c n ψ a i3 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a i4) else 0) := by
    intro i1 i2 i3 i4
    rw [← Finset.mul_sum, pauli_moment_two_eq_four_replica_sum_chi_sum]
    by_cases h : i1 + i2 + i3 + i4 = 0
    · simp only [h, if_true]; ring
    · simp only [h, if_false]; ring
  simp only [hstep2, pauli_moment_two_eq_four_replica_sum_S]
  rw [pauli_moment_two_eq_four_replica_sum_factor4]

private lemma pauli_moment_two_eq_four_replica_sum_fin2_add_eq_zero (a b : Fin 2) : a + b = 0 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> simp

private lemma pauli_moment_two_eq_four_replica_sum_add_eq_zero_iff {n : ℕ} (f g : Fin n → Fin 2) :
    f + g = 0 ↔ f = g := by
  constructor
  · intro h
    funext k
    have hk : f k + g k = 0 := by
      simpa only [Pi.add_apply, Pi.zero_apply] using congrFun h k
    exact (pauli_moment_two_eq_four_replica_sum_fin2_add_eq_zero (f k) (g k)).mp hk
  · rintro rfl
    funext k
    simp only [Pi.add_apply, Pi.zero_apply, pauli_moment_two_eq_four_replica_sum_fin2_add_eq_zero]

private lemma pauli_moment_two_eq_four_replica_sum_ite_reindex {n : ℕ} (f g k : Fin n → Fin 2) (A : (Fin n → Fin 2) → ℂ) :
    (∑ i : Fin n → Fin 2, (if f + g + k + i = 0 then A i else 0)) = A (f + g + k) := by
  have hsum : (∑ i : Fin n → Fin 2, (if f + g + k + i = 0 then A i else 0))
      = (∑ i : Fin n → Fin 2, (if i = f + g + k then A i else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hb : (f + g + k + i = 0)
    · rw [if_pos hb, if_pos ((pauli_moment_two_eq_four_replica_sum_add_eq_zero_iff (f + g + k) i).mp hb).symm]
    · rw [if_neg hb, if_neg (fun hc => hb ((pauli_moment_two_eq_four_replica_sum_add_eq_zero_iff (f + g + k) i).mpr hc.symm))]
  rw [hsum, Finset.sum_ite_eq']
  simp

private lemma pauli_moment_two_eq_four_replica_sum_S_reindex (n : ℕ) (ψ : Hn n) (a : Fin n → Fin 2) :
    pauli_moment_two_eq_four_replica_sum_S n ψ a = ∑ x1 : Fin n → Fin 2, ∑ x2 : Fin n → Fin 2, ∑ x3 : Fin n → Fin 2,
      pauli_moment_two_eq_four_replica_sum_c n ψ a x1 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a x2) *
        pauli_moment_two_eq_four_replica_sum_c n ψ a x3 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a (x1 + x2 + x3)) := by
  unfold pauli_moment_two_eq_four_replica_sum_S
  simp only [pauli_moment_two_eq_four_replica_sum_ite_reindex]

private lemma pauli_moment_two_eq_four_replica_sum_c_expand (n : ℕ) (ψ : Hn n) (a x1 x2 x3 : Fin n → Fin 2) :
    pauli_moment_two_eq_four_replica_sum_c n ψ a x1 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a x2) *
        pauli_moment_two_eq_four_replica_sum_c n ψ a x3 * starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_c n ψ a (x1 + x2 + x3))
      = starRingEnd ℂ (ψ x1) * ψ (x1 + a) * ψ x2 * starRingEnd ℂ (ψ (x2 + a)) *
        starRingEnd ℂ (ψ x3) * ψ (x3 + a) * ψ (x1 + x2 + x3) *
        starRingEnd ℂ (ψ ((x1 + x2 + x3) + a)) := by
  simp only [pauli_moment_two_eq_four_replica_sum_c, map_mul, starRingEnd_apply, star_star]
  ring

private lemma pauli_moment_two_eq_four_replica_sum_inv_mul_pow (n : ℕ) (X : ℂ) :
    (1 / (2:ℂ)^n) * ((2:ℂ)^n * X) = X := by
  have h : (2:ℂ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp

open scoped BigOperators Classical in
/-- The second Pauli-Liouville moment of any n-qubit pure state ψ expands as a 4-replica correlation sum over bit-flip shift a and replica bitstrings x1, x2, x3. -/
theorem pauli_moment_two_eq_four_replica_sum (n : ℕ) (ψ : Hn n) :
    (pauliLiouvilleMomentTwo n ψ : ℂ) =
      ∑ a : Fin n → Fin 2,
      ∑ x1 : Fin n → Fin 2,
      ∑ x2 : Fin n → Fin 2,
      ∑ x3 : Fin n → Fin 2,
        let x4 : Fin n → Fin 2 := fun v => x1 v + x2 v + x3 v
        starRingEnd ℂ (ψ x1) * ψ (fun v => x1 v + a v) *
        ψ x2 * starRingEnd ℂ (ψ (fun v => x2 v + a v)) *
        starRingEnd ℂ (ψ x3) * ψ (fun v => x3 v + a v) *
        ψ x4 * starRingEnd ℂ (ψ (fun v => x4 v + a v)) := by
  rw [pauli_moment_two_eq_four_replica_sum_moment_eq n ψ]
  rw [show (∑ p : PauliString n,
        (inner ℂ ψ (pauliOp p ψ))^2 * (starRingEnd ℂ (inner ℂ ψ (pauliOp p ψ)))^2)
      = ∑ p : PauliString n,
          (pauli_moment_two_eq_four_replica_sum_W n ψ (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k))
            (fun k => pauli_moment_two_eq_four_replica_sum_zs (p k)))^2 *
          (starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_W n ψ (fun k => pauli_moment_two_eq_four_replica_sum_xs (p k))
            (fun k => pauli_moment_two_eq_four_replica_sum_zs (p k))))^2 from
    Finset.sum_congr rfl (fun p _ => pauli_moment_two_eq_four_replica_sum_zsq_conjsq n ψ p)]
  rw [pauli_moment_two_eq_four_replica_sum_sum_bij n
    (fun a b => (pauli_moment_two_eq_four_replica_sum_W n ψ a b)^2 *
      (starRingEnd ℂ (pauli_moment_two_eq_four_replica_sum_W n ψ a b))^2)]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => pauli_moment_two_eq_four_replica_sum_sum_b_step n ψ a)]
  rw [Finset.mul_sum]
  simp only [pauli_moment_two_eq_four_replica_sum_inv_mul_pow]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => pauli_moment_two_eq_four_replica_sum_S_reindex n ψ a)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl
    (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => ?_))))
  exact pauli_moment_two_eq_four_replica_sum_c_expand n ψ a x1 x2 x3
