import AFTD.Prelude
import AFTD.Kb.Physics.XzRho
import AFTD.Kb.Tcs.PauliMatrix
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Physics.XzPauliString
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.PauliBasisToMatrix
import AFTD.Kb.Tcs.SigmaI
import AFTD.Kb.Tcs.SigmaX
import AFTD.Kb.Tcs.SigmaY
import AFTD.Kb.Tcs.SigmaZ
import AFTD.Kb.Tcs.G
import AFTD.Kb.Physics.XzPauli

/-!
# xz_rho_trace_one

Topic: quantum_mechanics   Node: a56d6b57b8e9

Provenance: helper lemma. arXiv:2610.20846, Appendix C

For every natural number L with 1 ≤ L, the trace of the reduced density matrix `xz_rho L` equals 1: `Matrix.trace (xz_rho L) = 1`.
-/

open scoped BigOperators
open Matrix

/-- Trace pairing of two single-qubit Pauli matrices: orthonormal up to a factor 2. -/
private lemma xz_rho_trace_one_pauli_basis_trace_mul (s t : PauliBasis) :
    Matrix.trace (PauliBasis.toMatrix s * PauliBasis.toMatrix t) = if s = t then (2:ℂ) else 0 := by
  fin_cases s <;> fin_cases t <;>
    simp [PauliBasis.toMatrix.eq_1, PauliBasis.toMatrix.eq_2, PauliBasis.toMatrix.eq_3,
      PauliBasis.toMatrix.eq_4, sigmaI, sigmaX, sigmaY, sigmaZ, Matrix.trace, Matrix.diag_apply,
      Fin.sum_univ_two, Complex.ext_iff] <;> norm_num

/-- Splitting a family indexed by pairs of functions into a single family of pointwise pairs. -/
private def xz_rho_trace_one_pi_prod_equiv {ι : Type*} (α β : ι → Type*) :
    (∀ i, α i × β i) ≃ (∀ i, α i) × (∀ i, β i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv f := by funext i; rfl
  right_inv p := by ext i <;> rfl

/-- A double sum over pairs of 2-valued functions is a single sum over pointwise pairs. -/
private lemma xz_rho_trace_one_sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*}
    [AddCommMonoid M] (f : (ι → Fin 2) → (ι → Fin 2) → M) :
    (∑ i, ∑ j, f i j) = ∑ c : ι → (Fin 2 × Fin 2), f (fun k => (c k).1) (fun k => (c k).2) := by
  refine (Fintype.sum_prod_type (fun p : (ι → Fin 2) × (ι → Fin 2) => f p.1 p.2)).symm.trans ?_
  exact (Equiv.sum_comp (xz_rho_trace_one_pi_prod_equiv (fun _ => Fin 2) (fun _ => Fin 2))
    (fun p => f p.1 p.2)).symm

/-- The trace of a product of two Pauli string matrices is the product of the single-site traces. -/
private lemma xz_rho_trace_one_trace_pauliMatrix_mul {n : ℕ} (p q : PauliString n) :
    Matrix.trace (pauliMatrix p * pauliMatrix q)
      = ∏ k, Matrix.trace ((p k).toMatrix * (q k).toMatrix) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pauliMatrix]
  simp only [← Finset.prod_mul_distrib]
  rw [xz_rho_trace_one_sum_pi_prod]
  rw [← Fintype.piFinset_univ]
  rw [Finset.sum_prod_piFinset (s := Finset.univ) (κ := Fin 2 × Fin 2)
      (g := fun k z => (p k).toMatrix z.1 z.2 * (q k).toMatrix z.2 z.1)]
  simp only [Fintype.sum_prod_type]

/-- Self-pairing of a Pauli string matrix: trace of the square is `2 ^ n`. -/
private lemma xz_rho_trace_one_pauli_trace_mul_self {n : ℕ} (p : PauliString n) :
    Matrix.trace (pauliMatrix p * pauliMatrix p) = (2:ℂ)^n := by
  rw [xz_rho_trace_one_trace_pauliMatrix_mul]
  simp [xz_rho_trace_one_pauli_basis_trace_mul, Finset.prod_const]

/-- Distinct Pauli strings are orthogonal in the trace pairing. -/
private lemma xz_rho_trace_one_pauli_trace_mul_of_ne {n : ℕ} {p q : PauliString n} (h : p ≠ q) :
    Matrix.trace (pauliMatrix p * pauliMatrix q) = 0 := by
  classical
  rw [xz_rho_trace_one_trace_pauliMatrix_mul]
  simp only [xz_rho_trace_one_pauli_basis_trace_mul]
  obtain ⟨k, hk⟩ : ∃ k, p k ≠ q k := by
    by_contra hk
    push Not at hk
    exact h (funext hk)
  exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- `xz_pauli` recovers its first argument. -/
private lemma xz_rho_trace_one_xz_pauli_fst {a b a' b' : Fin 2}
    (h : xz_pauli a b = xz_pauli a' b') : a = a' := by
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;> simp_all [xz_pauli]

/-- `xz_pauli_string L` is injective. -/
private lemma xz_rho_trace_one_injective (L : ℕ) : Function.Injective (xz_pauli_string L) := by
  intro a b hab
  funext j
  have h := congrFun hab j
  simp only [xz_pauli_string] at h
  exact xz_rho_trace_one_xz_pauli_fst h

/-- The reduced density matrix rho_L has unit trace for any L >= 1. -/
theorem xz_rho_trace_one (L : ℕ) (hL : 1 ≤ L) : Matrix.trace (xz_rho L) = 1 := by
  classical
  have hinj := xz_rho_trace_one_injective L
  have hsum : ∀ a b : Fin L → Fin 2,
      Matrix.trace (pauliMatrix (xz_pauli_string L a) * pauliMatrix (xz_pauli_string L b))
        = if a = b then (2:ℂ)^L else 0 := by
    intro a b
    by_cases h : a = b
    · subst h; simp [xz_rho_trace_one_pauli_trace_mul_self]
    · rw [if_neg h, xz_rho_trace_one_pauli_trace_mul_of_ne]
      intro hcontra
      exact h (hinj hcontra)
  have hSS : (∑ a : Fin L → Fin 2, pauliMatrix (xz_pauli_string L a)) *
      (∑ a : Fin L → Fin 2, pauliMatrix (xz_pauli_string L a))
      = ∑ a : Fin L → Fin 2, ∑ b : Fin L → Fin 2,
          pauliMatrix (xz_pauli_string L a) * pauliMatrix (xz_pauli_string L b) := by
    rw [Matrix.sum_mul]
    simp only [Matrix.mul_sum]
  simp only [xz_rho, xz_matrix_a, hSS, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_sum]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsum a b))]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hcard : Fintype.card (Fin L → Fin 2) = 2 ^ L := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  push_cast
  have h2 : ((2:ℂ))^L ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
