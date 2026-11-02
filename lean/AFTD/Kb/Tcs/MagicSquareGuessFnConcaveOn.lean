import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareGuessFn
import AFTD.Kb.Tcs.MagicSquareStrategyValid
import AFTD.Kb.Tcs.MagicSquareKeyGuessSuccess
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal
import AFTD.Kb.Tcs.IsPovm
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Tcs.MagicSquareScore
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace

/-!
# magic_square_guess_fn_concaveOn

Topic: quantum   Node: 3efacbdff32f

Provenance: original. Related work: OP-730: arXiv:2610.12001 (Exact value and rigidity of the 2x3 magic rectangle), Sec. 8 asks for the exact function g(w) and its slope c* at the threshold; Corollary 6.2 bounds 1 - g(β₀+δ) between (9/2)δ and 3δ/(4(1-β₀)).

The function g = magic_square_guess_fn — g(w) is the supremum of the adversary's probability of guessing Alice's complete first-row answer in the magic-square game, over finite-dimensional strategies with quantum side information and score at least w — is concave on the interval (-∞, 1] (ConcaveOn ℝ (Set.Iic 1)).
-/

namespace MagicSquareConcave
open Matrix
open scoped Kronecker
open scoped ComplexOrder

@[simp] lemma castAdd_eq_natAdd_iff {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i = Fin.natAdd n j ↔ False := by
  simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, iff_false]; omega

@[simp] lemma natAdd_eq_castAdd_iff {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.natAdd n j = Fin.castAdd m i ↔ False := by
  simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, iff_false]; omega

/-- inclusion of the first block -/
def incL (n m : ℕ) : Matrix (Fin n) (Fin (n + m)) ℂ :=
  Matrix.of fun i j => if j = Fin.castAdd m i then 1 else 0

def incR (n m : ℕ) : Matrix (Fin m) (Fin (n + m)) ℂ :=
  Matrix.of fun i j => if j = Fin.natAdd n i then 1 else 0

lemma incL_mul_conj (n m : ℕ) : incL n m * (incL n m)ᴴ = 1 := by
  ext i i'
  simp [incL, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

lemma incR_mul_conj (n m : ℕ) : incR n m * (incR n m)ᴴ = 1 := by
  ext i i'
  simp [incR, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

lemma incL_mul_conjR (n m : ℕ) : incL n m * (incR n m)ᴴ = 0 := by
  ext i i'
  simp [incL, incR, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma incR_mul_conjL (n m : ℕ) : incR n m * (incL n m)ᴴ = 0 := by
  ext i i'
  simp [incL, incR, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma conj_inc_add (n m : ℕ) :
    (incL n m)ᴴ * incL n m + (incR n m)ᴴ * incR n m = 1 := by
  ext j j'
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) j' <;>
  simp [incL, incR, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

/-- block-diagonal sum -/
def blk {n m : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin (n + m)) (Fin (n + m)) ℂ :=
  (incL n m)ᴴ * X * incL n m + (incR n m)ᴴ * Y * incR n m

lemma compL_blk {n m : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    incL n m * blk X Y * (incL n m)ᴴ = X := by
  simp only [blk, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, incL_mul_conj,
    incL_mul_conjR, Matrix.one_mul, Matrix.zero_mul]
  simp [Matrix.mul_assoc, incL_mul_conj]

lemma compR_blk {n m : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    incR n m * blk X Y * (incR n m)ᴴ = Y := by
  simp only [blk, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, incR_mul_conj,
    incR_mul_conjL, Matrix.one_mul, Matrix.zero_mul]
  simp [Matrix.mul_assoc, incR_mul_conj]

lemma blk_psd {n m : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} {Y : Matrix (Fin m) (Fin m) ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : (blk X Y).PosSemidef :=
  (hX.conjTranspose_mul_mul_same _).add (hY.conjTranspose_mul_mul_same _)

lemma blk_zero (n m : ℕ) : blk (0 : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) = 0 := by
  simp [blk]

lemma blk_one (n m : ℕ) : blk (1 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  simp [blk, conj_inc_add]

lemma blk_sum {n m : ℕ} {ι : Type} [Fintype ι] (X : ι → Matrix (Fin n) (Fin n) ℂ)
    (Y : ι → Matrix (Fin m) (Fin m) ℂ) : ∑ i, blk (X i) (Y i) = blk (∑ i, X i) (∑ i, Y i) := by
  simp [blk, Finset.sum_add_distrib, Matrix.sum_mul, Matrix.mul_sum]

lemma blk_povm {n m : ℕ} {ι : Type} [Fintype ι] {X : ι → Matrix (Fin n) (Fin n) ℂ}
    {Y : ι → Matrix (Fin m) (Fin m) ℂ} (hX : is_povm n X) (hY : is_povm m Y) :
    is_povm (n + m) (fun i => blk (X i) (Y i)) :=
  ⟨fun i => blk_psd (hX.1 i) (hY.1 i), by rw [blk_sum, hX.2, hY.2, blk_one]⟩

/-- the trace-linear-form fact: compression through a Kronecker isometry -/
lemma tr_kron_conj {a a' b b' e e' : ℕ}
    (VA : Matrix (Fin a) (Fin a') ℂ) (VB : Matrix (Fin b) (Fin b') ℂ) (VE : Matrix (Fin e) (Fin e') ℂ)
    (X : Matrix (Fin a') (Fin a') ℂ) (Y : Matrix (Fin b') (Fin b') ℂ) (Z : Matrix (Fin e') (Fin e') ℂ)
    (ρ : Matrix ((Fin a × Fin b) × Fin e) ((Fin a × Fin b) × Fin e) ℂ) :
    (((X ⊗ₖ Y) ⊗ₖ Z) * (((VAᴴ ⊗ₖ VBᴴ) ⊗ₖ VEᴴ) * ρ * ((VAᴴ ⊗ₖ VBᴴ) ⊗ₖ VEᴴ)ᴴ)).trace =
      ((((VA * X * VAᴴ) ⊗ₖ (VB * Y * VBᴴ)) ⊗ₖ (VE * Z * VEᴴ)) * ρ).trace := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  congr 2
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_kronecker_mul, Matrix.mul_assoc]


lemma compL_one (n m : ℕ) : incL n m * (1 : Matrix (Fin (n + m)) (Fin (n + m)) ℂ) * (incL n m)ᴴ = 1 := by
  rw [Matrix.mul_one, incL_mul_conj]

lemma compR_one (n m : ℕ) : incR n m * (1 : Matrix (Fin (n + m)) (Fin (n + m)) ℂ) * (incR n m)ᴴ = 1 := by
  rw [Matrix.mul_one, incR_mul_conj]

lemma iso_trace {a a' b b' e e' : ℕ}
    (VA : Matrix (Fin a') (Fin a) ℂ) (VB : Matrix (Fin b') (Fin b) ℂ) (VE : Matrix (Fin e') (Fin e) ℂ)
    (hA : VA * VAᴴ = 1) (hB : VB * VBᴴ = 1) (hE : VE * VEᴴ = 1)
    (ρ : Matrix ((Fin a' × Fin b') × Fin e') ((Fin a' × Fin b') × Fin e') ℂ) :
    (((VAᴴ ⊗ₖ VBᴴ) ⊗ₖ VEᴴ) * ρ * ((VAᴴ ⊗ₖ VBᴴ) ⊗ₖ VEᴴ)ᴴ).trace = ρ.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_kronecker_mul, hA, hB, hE, Matrix.one_kronecker_one, Matrix.one_mul]

section mix
variable {dA1 dB1 dE1 dA2 dB2 dE2 : ℕ}

noncomputable def mixρ (a b : ℝ)
    (ρ1 : Matrix ((Fin dA1 × Fin dB1) × Fin dE1) ((Fin dA1 × Fin dB1) × Fin dE1) ℂ)
    (ρ2 : Matrix ((Fin dA2 × Fin dB2) × Fin dE2) ((Fin dA2 × Fin dB2) × Fin dE2) ℂ) :
    Matrix ((Fin (dA1 + dA2) × Fin (dB1 + dB2)) × Fin (dE1 + dE2))
      ((Fin (dA1 + dA2) × Fin (dB1 + dB2)) × Fin (dE1 + dE2)) ℂ :=
  (a : ℂ) • ((((incL dA1 dA2)ᴴ ⊗ₖ (incL dB1 dB2)ᴴ) ⊗ₖ (incL dE1 dE2)ᴴ) * ρ1 *
      (((incL dA1 dA2)ᴴ ⊗ₖ (incL dB1 dB2)ᴴ) ⊗ₖ (incL dE1 dE2)ᴴ)ᴴ) +
    (b : ℂ) • ((((incR dA1 dA2)ᴴ ⊗ₖ (incR dB1 dB2)ᴴ) ⊗ₖ (incR dE1 dE2)ᴴ) * ρ2 *
      (((incR dA1 dA2)ᴴ ⊗ₖ (incR dB1 dB2)ᴴ) ⊗ₖ (incR dE1 dE2)ᴴ)ᴴ)

lemma tr_mix (a b : ℝ)
    (ρ1 : Matrix ((Fin dA1 × Fin dB1) × Fin dE1) ((Fin dA1 × Fin dB1) × Fin dE1) ℂ)
    (ρ2 : Matrix ((Fin dA2 × Fin dB2) × Fin dE2) ((Fin dA2 × Fin dB2) × Fin dE2) ℂ)
    (X1 : Matrix (Fin dA1) (Fin dA1) ℂ) (X2 : Matrix (Fin dA2) (Fin dA2) ℂ)
    (Y1 : Matrix (Fin dB1) (Fin dB1) ℂ) (Y2 : Matrix (Fin dB2) (Fin dB2) ℂ)
    (Z1 : Matrix (Fin dE1) (Fin dE1) ℂ) (Z2 : Matrix (Fin dE2) (Fin dE2) ℂ) :
    (((blk X1 X2 ⊗ₖ blk Y1 Y2) ⊗ₖ blk Z1 Z2) * mixρ a b ρ1 ρ2).trace.re =
      a * (((X1 ⊗ₖ Y1) ⊗ₖ Z1) * ρ1).trace.re + b * (((X2 ⊗ₖ Y2) ⊗ₖ Z2) * ρ2).trace.re := by
  rw [mixρ, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, tr_kron_conj,
    tr_kron_conj, compL_blk, compL_blk, compL_blk, compR_blk, compR_blk, compR_blk]
  simp [Complex.add_re]

lemma blk_one' (n m : ℕ) : (1 : Matrix (Fin (n + m)) (Fin (n + m)) ℂ) = blk 1 1 := (blk_one n m).symm

open scoped ComplexOrder in
lemma mixρ_valid (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {A1 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA1) (Fin dA1) ℂ}
    {B1 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB1) (Fin dB1) ℂ}
    {ρ1 : Matrix ((Fin dA1 × Fin dB1) × Fin dE1) ((Fin dA1 × Fin dB1) × Fin dE1) ℂ}
    {A2 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA2) (Fin dA2) ℂ}
    {B2 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB2) (Fin dB2) ℂ}
    {ρ2 : Matrix ((Fin dA2 × Fin dB2) × Fin dE2) ((Fin dA2 × Fin dB2) × Fin dE2) ℂ}
    (h1 : magic_square_strategy_valid A1 B1 ρ1) (h2 : magic_square_strategy_valid A2 B2 ρ2) :
    magic_square_strategy_valid (fun x s => blk (A1 x s) (A2 x s)) (fun j c => blk (B1 j c) (B2 j c))
      (mixρ a b ρ1 ρ2) := by
  obtain ⟨hA1, hA1z, hB1, hB1z, hρ1, htr1⟩ := h1
  obtain ⟨hA2, hA2z, hB2, hB2z, hρ2, htr2⟩ := h2
  refine ⟨fun x => blk_povm (hA1 x) (hA2 x), fun x s hs => ?_, fun j => blk_povm (hB1 j) (hB2 j),
    fun j c hc => ?_, ?_, ?_⟩
  · simp only [hA1z x s hs, hA2z x s hs, blk_zero]
  · simp only [hB1z j c hc, hB2z j c hc, blk_zero]
  · refine Matrix.PosSemidef.add ((hρ1.mul_mul_conjTranspose_same _).smul ?_)
      ((hρ2.mul_mul_conjTranspose_same _).smul ?_)
    · exact_mod_cast ha
    · exact_mod_cast hb
  · rw [mixρ, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      iso_trace _ _ _ (incL_mul_conj _ _) (incL_mul_conj _ _) (incL_mul_conj _ _),
      iso_trace _ _ _ (incR_mul_conj _ _) (incR_mul_conj _ _) (incR_mul_conj _ _), htr1, htr2]
    simp only [smul_eq_mul, mul_one]
    exact_mod_cast hab

lemma mix_score (a b : ℝ)
    (A1 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA1) (Fin dA1) ℂ)
    (B1 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB1) (Fin dB1) ℂ)
    (ρ1 : Matrix ((Fin dA1 × Fin dB1) × Fin dE1) ((Fin dA1 × Fin dB1) × Fin dE1) ℂ)
    (A2 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA2) (Fin dA2) ℂ)
    (B2 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB2) (Fin dB2) ℂ)
    (ρ2 : Matrix ((Fin dA2 × Fin dB2) × Fin dE2) ((Fin dA2 × Fin dB2) × Fin dE2) ℂ) :
    magic_square_score (fun x s => blk (A1 x s) (A2 x s)) (fun j c => blk (B1 j c) (B2 j c))
      (mixρ a b ρ1 ρ2) = a * magic_square_score A1 B1 ρ1 + b * magic_square_score A2 B2 ρ2 := by
  simp only [magic_square_score, blk_one', tr_mix]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> ring

lemma mix_guess (a b : ℝ)
    (A1 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA1) (Fin dA1) ℂ)
    (ρ1 : Matrix ((Fin dA1 × Fin dB1) × Fin dE1) ((Fin dA1 × Fin dB1) × Fin dE1) ℂ)
    (M1 : (Fin 3 → Bool) → Matrix (Fin dE1) (Fin dE1) ℂ)
    (A2 : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA2) (Fin dA2) ℂ)
    (ρ2 : Matrix ((Fin dA2 × Fin dB2) × Fin dE2) ((Fin dA2 × Fin dB2) × Fin dE2) ℂ)
    (M2 : (Fin 3 → Bool) → Matrix (Fin dE2) (Fin dE2) ℂ) :
    magic_square_key_guess_success (fun x s => blk (A1 x s) (A2 x s)) (mixρ a b ρ1 ρ2)
      (fun k => blk (M1 k) (M2 k)) =
      a * magic_square_key_guess_success A1 ρ1 M1 + b * magic_square_key_guess_success A2 ρ2 M2 := by
  simp only [magic_square_key_guess_success, blk_one', tr_mix]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]

end mix


def Obs : Fin 3 → Fin 3 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![![!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]],
    ![!![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1],
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1],
      !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]],
    ![!![0, 0, -1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, 1, 0, 0],
      !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
      !![0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0]]]

def perf_sg (b : Bool) : ℤ := if b then -1 else 1

def PA (x : Fin 3) (s : Fin 3 → Bool) : Matrix (Fin 4) (Fin 4) ℤ :=
  if xor (xor (s 0) (s 1)) (s 2) = true then 0 else
    (1 + perf_sg (s 0) • Obs x 0) * (1 + perf_sg (s 1) • Obs x 1)

def PB (j : Fin 3) (c : Fin 3 → Bool) : Matrix (Fin 4) (Fin 4) ℤ :=
  if xor (xor (c 0) (c 1)) (c 2) = false then 0 else
    (1 + perf_sg (c 0) • Obs 0 j) * (1 + perf_sg (c 1) • Obs 1 j)

set_option maxRecDepth 100000 in
theorem PA_proj : ∀ x s, PA x s * PA x s = 4 • PA x s ∧ (PA x s).transpose = PA x s := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem PB_proj : ∀ j c, PB j c * PB j c = 4 • PB j c ∧ (PB j c).transpose = PB j c := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem PA_sum : ∀ x, ∑ s, PA x s = 4 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem PB_sum : ∀ j, ∑ c, PB j c = 4 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem win_sum : (∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool, ∑ c : Fin 3 → Bool,
    if s j = c x then ∑ a : Fin 4, ∑ a' : Fin 4, PA x s a a' * PB j c a a' else 0) = 576 := by
  decide +kernel


open Matrix in
noncomputable def Ac (x : Fin 3) (s : Fin 3 → Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 4 : ℂ) • (Int.castRingHom ℂ).mapMatrix (PA x s)

open Matrix in
noncomputable def Bc (j : Fin 3) (c : Fin 3 → Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 4 : ℂ) • (Int.castRingHom ℂ).mapMatrix (PB j c)

noncomputable def perf_psi : (Fin 4 × Fin 4) × Fin 1 → ℂ := fun i => if i.1.1 = i.1.2 then 1 / 2 else 0

noncomputable def ρc : Matrix ((Fin 4 × Fin 4) × Fin 1) ((Fin 4 × Fin 4) × Fin 1) ℂ :=
  Matrix.vecMulVec perf_psi (star perf_psi)

open Matrix in
open scoped ComplexOrder in
lemma psd_of_proj (P : Matrix (Fin 4) (Fin 4) ℤ) (h : P * P = 4 • P ∧ P.transpose = P) :
    ((1 / 4 : ℂ) • (Int.castRingHom ℂ).mapMatrix P).PosSemidef := by
  have hc : ((1 / 4 : ℂ) • (Int.castRingHom ℂ).mapMatrix P)ᴴ = (1 / 4 : ℂ) • (Int.castRingHom ℂ).mapMatrix P := by
    ext i j
    have := congrFun (congrFun h.2 i) j
    simp only [Matrix.transpose_apply] at this
    simp [Matrix.conjTranspose_apply, this]
  have hm : (1 / 4 : ℂ) • (Int.castRingHom ℂ).mapMatrix P =
      ((1 / 4 : ℂ) • (Int.castRingHom ℂ).mapMatrix P) * ((1 / 4 : ℂ) • (Int.castRingHom ℂ).mapMatrix P)ᴴ := by
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, ← map_mul, h.1, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, smul_smul]
    norm_num
  rw [hm]
  exact Matrix.posSemidef_self_mul_conjTranspose _

lemma perf_tr_rho (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    (((X ⊗ₖ Y) ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) * ρc).trace =
      (1 / 4) * ∑ a : Fin 4, ∑ a' : Fin 4, X a a' * Y a a' := by
  simp [Matrix.trace, Matrix.mul_apply, ρc, Matrix.vecMulVec_apply, perf_psi, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Fin.sum_univ_four, map_ofNat]
  ring

open scoped ComplexOrder in
lemma perf_valid : magic_square_strategy_valid Ac Bc ρc := by
  refine ⟨fun x => ⟨fun s => psd_of_proj _ (PA_proj x s), ?_⟩, fun x s hs => ?_,
    fun j => ⟨fun c => psd_of_proj _ (PB_proj j c), ?_⟩, fun j c hc => ?_, ?_, ?_⟩
  · simp only [Ac]
    rw [← Finset.smul_sum, ← map_sum, PA_sum, map_nsmul, map_one, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num
  · simp [Ac, PA, hs]
  · simp only [Bc]
    rw [← Finset.smul_sum, ← map_sum, PB_sum, map_nsmul, map_one, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num
  · simp [Bc, PB, hc]
  · exact Matrix.posSemidef_vecMulVec_self_star perf_psi
  · simp [ρc, Matrix.trace, Matrix.vecMulVec_apply, perf_psi, Fintype.sum_prod_type, map_ofNat]
    norm_num

lemma perf_entry (x j : Fin 3) (s c : Fin 3 → Bool) :
    (((Ac x s ⊗ₖ Bc j c) ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) * ρc).trace.re =
      1 / 64 * ((∑ a : Fin 4, ∑ a' : Fin 4, PA x s a a' * PB j c a a' : ℤ) : ℝ) := by
  rw [perf_tr_rho]
  have : (1 / 4 : ℂ) * ∑ a : Fin 4, ∑ a' : Fin 4, Ac x s a a' * Bc j c a a' =
      ((1 / 64 * ((∑ a : Fin 4, ∑ a' : Fin 4, PA x s a a' * PB j c a a' : ℤ) : ℝ) : ℝ) : ℂ) := by
    simp only [Ac, Bc, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast,
      smul_eq_mul]
    push_cast
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    ring
  rw [this, Complex.ofReal_re]

lemma score_one : magic_square_score Ac Bc ρc = 1 := by
  have h := congrArg (Int.cast : ℤ → ℝ) win_sum
  push_cast at h
  have : magic_square_score Ac Bc ρc = 1 / 576 * (∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool,
      ∑ c : Fin 3 → Bool, if s j = c x then ∑ a : Fin 4, ∑ a' : Fin 4,
        ((PA x s a a' : ℝ) * (PB j c a a' : ℝ)) else 0) := by
    rw [magic_square_score]
    simp only [perf_entry, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · push_cast; simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
      ring
    · simp
  rw [this, h]
  norm_num


open scoped ComplexOrder MatrixOrder in
lemma tr_psd_mul {n : Type} [Fintype n] [DecidableEq n] {P ρ : Matrix n n ℂ} (hP : P.PosSemidef)
    (hρ : ρ.PosSemidef) : 0 ≤ (P * ρ).trace.re := by
  obtain ⟨X, hX, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hP.isHermitian
    (QuasispectrumRestricts.nnreal_of_nonneg hP.nonneg)
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
  have h := hρ.mul_mul_conjTranspose_same X
  rw [← Matrix.star_eq_conjTranspose, hX.star_eq] at h
  exact (Complex.nonneg_iff.1 h.trace_nonneg).1

open scoped ComplexOrder in
lemma one_sub_povm {d : ℕ} {M : (Fin 3 → Bool) → Matrix (Fin d) (Fin d) ℂ} (hM : is_povm d M)
    (k : Fin 3 → Bool) : (1 - M k).PosSemidef := by
  have : 1 - M k = ∑ i ∈ Finset.univ.erase k, M i := by
    rw [← hM.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    abel
  rw [this]
  exact Matrix.posSemidef_sum _ fun i _ => hM.1 i

lemma guess_le_one {dA dB dE : ℕ}
    {A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ}
    {B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ}
    {ρ : Matrix ((Fin dA × Fin dB) × Fin dE) ((Fin dA × Fin dB) × Fin dE) ℂ}
    {M : (Fin 3 → Bool) → Matrix (Fin dE) (Fin dE) ℂ}
    (hv : magic_square_strategy_valid A B ρ) (hM : is_povm dE M) :
    magic_square_key_guess_success A ρ M ≤ 1 := by
  obtain ⟨hA, -, -, -, hρ, htr⟩ := hv
  have key : ∀ k, (((A 0 k ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ M k) * ρ).trace.re ≤
      (((A 0 k ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ (1 : Matrix (Fin dE) (Fin dE) ℂ)) * ρ).trace.re := by
    intro k
    have h := tr_psd_mul (((hA 0).1 k).kronecker Matrix.PosSemidef.one |>.kronecker (one_sub_povm hM k)) hρ
    have hk : ((A 0 k ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ (1 - M k)) =
        ((A 0 k ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ 1) - ((A 0 k ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ M k) := by
      rw [eq_sub_iff_add_eq, ← Matrix.kronecker_add, sub_add_cancel]
    rw [hk, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at h
    linarith
  have hsum : ∑ k, (((A 0 k ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ (1 : Matrix (Fin dE) (Fin dE) ℂ)) * ρ).trace.re = 1 := by
    have h1 : ∑ k, ((A 0 k ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ (1 : Matrix (Fin dE) (Fin dE) ℂ)) = 1 := by
      have h2 : ∑ k, ((A 0 k ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ (1 : Matrix (Fin dE) (Fin dE) ℂ)) =
          (((∑ k, A 0 k) ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ (1 : Matrix (Fin dE) (Fin dE) ℂ)) := by
        ext i j
        simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
      rw [h2, (hA 0).2, Matrix.one_kronecker_one, Matrix.one_kronecker_one]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, h1, Matrix.one_mul, htr, Complex.one_re]
  rw [magic_square_key_guess_success, ← hsum]
  exact Finset.sum_le_sum fun k _ => key k

def gset (w : ℝ) : Set ℝ :=
  {p : ℝ | ∃ (dA dB dE : ℕ) (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix ((Fin dA × Fin dB) × Fin dE) ((Fin dA × Fin dB) × Fin dE) ℂ)
    (M : (Fin 3 → Bool) → Matrix (Fin dE) (Fin dE) ℂ),
    magic_square_strategy_valid A B ρ ∧ is_povm dE M ∧ w ≤ magic_square_score A B ρ ∧
      p = magic_square_key_guess_success A ρ M}

lemma g_eq (w : ℝ) : magic_square_guess_fn w = sSup (gset w) := rfl

lemma gset_bdd (w : ℝ) : BddAbove (gset w) := by
  refine ⟨1, ?_⟩
  rintro p ⟨dA, dB, dE, A, B, ρ, M, hv, hM, -, rfl⟩
  exact guess_le_one hv hM

noncomputable def M0 : (Fin 3 → Bool) → Matrix (Fin 1) (Fin 1) ℂ :=
  fun k => if k = (fun _ => false) then 1 else 0

open scoped ComplexOrder in
lemma M0_povm : is_povm 1 M0 := by
  refine ⟨fun k => ?_, ?_⟩
  · unfold M0
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  · simp [M0]

lemma gset_nonempty {w : ℝ} (hw : w ≤ 1) : (gset w).Nonempty :=
  ⟨_, 4, 4, 1, Ac, Bc, ρc, M0, perf_valid, M0_povm, hw.trans score_one.ge, rfl⟩

lemma gset_mix {w1 w2 p1 p2 a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h1 : p1 ∈ gset w1) (h2 : p2 ∈ gset w2) : a * p1 + b * p2 ∈ gset (a * w1 + b * w2) := by
  obtain ⟨dA1, dB1, dE1, A1, B1, ρ1, M1, hv1, hM1, hs1, rfl⟩ := h1
  obtain ⟨dA2, dB2, dE2, A2, B2, ρ2, M2, hv2, hM2, hs2, rfl⟩ := h2
  refine ⟨dA1 + dA2, dB1 + dB2, dE1 + dE2, fun x s => blk (A1 x s) (A2 x s),
    fun j c => blk (B1 j c) (B2 j c), mixρ a b ρ1 ρ2, fun k => blk (M1 k) (M2 k),
    mixρ_valid a b ha hb hab hv1 hv2, blk_povm hM1 hM2, ?_, ?_⟩
  · rw [mix_score]
    exact add_le_add (mul_le_mul_of_nonneg_left hs1 ha) (mul_le_mul_of_nonneg_left hs2 hb)
  · rw [mix_guess]

end MagicSquareConcave

theorem magic_square_guess_fn_concaveOn : ConcaveOn ℝ (Set.Iic 1) magic_square_guess_fn := by
  refine ⟨convex_Iic 1, fun w1 hw1 w2 hw2 a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, MagicSquareConcave.g_eq]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p1, hp1, hlt1⟩ := exists_lt_of_lt_csSup (MagicSquareConcave.gset_nonempty hw1)
    (sub_lt_self (sSup (MagicSquareConcave.gset w1)) hε)
  obtain ⟨p2, hp2, hlt2⟩ := exists_lt_of_lt_csSup (MagicSquareConcave.gset_nonempty hw2)
    (sub_lt_self (sSup (MagicSquareConcave.gset w2)) hε)
  have hle := le_csSup (MagicSquareConcave.gset_bdd _) (MagicSquareConcave.gset_mix ha hb hab hp1 hp2)
  have e1 := mul_le_mul_of_nonneg_left hlt1.le ha
  have e2 := mul_le_mul_of_nonneg_left hlt2.le hb
  nlinarith
