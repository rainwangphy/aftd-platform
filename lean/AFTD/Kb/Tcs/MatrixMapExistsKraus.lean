import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap
import AFTD.Kb.Tcs.MatrixMapOfKraus
import AFTD.Kb.Tcs.MatrixMapChoiMatrixInj
import AFTD.Kb.Tcs.MatrixMapChoiMatrix
import AFTD.Kb.Tcs.MatrixMapMapChoiInv
import AFTD.Kb.Tcs.MatrixMapChoiMapInv

/-!
# MatrixMap.exists_kraus

Topic: quantum   Node: d0eefb7492d3

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.exists_kraus`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixMap.exists_kraus
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixMap in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [CommSemiring R] [StarRing R] [Fintype B] in
theorem MatrixMap.exists_kraus (Φ : MatrixMap A B R) :
    ∃ r : ℕ, ∃ (M N : Fin r → Matrix B A R), Φ = of_kraus M N := by
  classical
  let K := ((B × A) × A) × B
  let M₀ : K → Matrix B A R := fun (((b, a₁), a₂), b₂) =>
    Matrix.single b a₁ (Φ (Matrix.single a₁ a₂ (1 : R)) b b₂)
  let N₀ : K → Matrix B A R := fun (((_, _), a₂), b₂) => Matrix.single b₂ a₂ (1 : R)
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin _).symm
  refine ⟨Fintype.card K, M₀ ∘ e, N₀ ∘ e, ?_⟩
  apply choi_matrix_inj
  ext ⟨j₁, i₁⟩ ⟨j₂, i₂⟩
  simp only [choi_matrix, of_kraus, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply]
  have hsum_reindex :
      (∑ x : Fin (Fintype.card K),
          (M₀ ∘ e) x * Matrix.single i₁ i₂ (1 : R) * ((N₀ ∘ e) x).conjTranspose) j₁ j₂
        =
      ∑ y : K, (M₀ y * Matrix.single i₁ i₂ (1 : R) * (N₀ y).conjTranspose) j₁ j₂ := by
    rw [Matrix.sum_apply]
    exact e.sum_comp
      (fun y : K => (M₀ y * Matrix.single i₁ i₂ (1 : R) * (N₀ y).conjTranspose) j₁ j₂)
  rw [hsum_reindex, Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [M₀, N₀, Matrix.mul_apply, Matrix.single, ite_and]
  rw [Finset.sum_eq_single i₂]
  · rw [Finset.sum_eq_single j₂]
    · simp
    · intro b hb hbj
      simp [hbj, star_zero]
    · simp
  · intro a ha ha_ne
    simp [ha_ne, star_zero]
  · simp
