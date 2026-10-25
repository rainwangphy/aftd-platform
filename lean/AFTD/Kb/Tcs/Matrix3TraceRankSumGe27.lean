import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TraceSplitReconstruction

/-!
# matrix3_trace_rank_sum_ge_27

Topic: algebraic_complexity   Node: b4179f55395e

Provenance: formalization of a published result. Source: arXiv:2610.11823v3, Lemma 4.1 (split flattening). The proof here uses a surjective linear map from the product of the first-factor column ranges and applies over every field; the paper states the two-element-field case.

For a finite family of 3x3 matrices over a field satisfying the cyclic trace identities of matrix multiplication, the sum of the matrix ranks of the first factors is at least 27.
-/

open Matrix Finset
noncomputable section
variable {K : Type*} [Field K] {r : ℕ}

private abbrev matrix3_factor_space (a : Fin r → Matrix (Fin 3) (Fin 3) K) :=
  ∀ s, LinearMap.range (a s).mulVecLin

private def matrix3_factor_map (a b : Fin r → Matrix (Fin 3) (Fin 3) K) :
    matrix3_factor_space a →ₗ[K] (Fin 3 × Fin 3 × Fin 3 → K) where
  toFun x p := ∑ s, (x s).val p.1 * b s p.2.1 p.2.2
  map_add' x y := by
    ext p
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    ext p
    simp [Finset.mul_sum, mul_assoc]

private def matrix3_factor_preimage (a c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (z : Fin 3 × Fin 3 × Fin 3 → K) : matrix3_factor_space a :=
  fun s => ⟨(a s).mulVecLin (fun j => ∑ k, ∑ i, c s k i * z (i,j,k)),
    ⟨_, rfl⟩⟩

private theorem matrix3_factor_reconstruction (a b c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0)
    (z : Fin 3 × Fin 3 × Fin 3 → K) :
    matrix3_factor_map a b (matrix3_factor_preimage a c z) = z := by
  ext p
  exact matrix3_trace_split_reconstruction a b c h z p

theorem matrix3_trace_rank_sum_ge_27 {K : Type*} [Field K] {r : ℕ} (a b c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0) :
    27 ≤ ∑ s, (a s).rank := by
  have hs : Function.Surjective (matrix3_factor_map a b) := fun z =>
    ⟨matrix3_factor_preimage a c z, matrix3_factor_reconstruction a b c h z⟩
  have hd := LinearMap.finrank_le_finrank_of_surjective hs
  simpa [matrix3_factor_space, Matrix.rank, Module.finrank_pi, Module.finrank_pi_fintype] using hd
