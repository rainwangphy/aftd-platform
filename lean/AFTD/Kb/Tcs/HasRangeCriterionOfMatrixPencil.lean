import AFTD.Prelude
import AFTD.Kb.Tcs.HasRangeCriterionSubspaces

/-!
# has_range_criterion_of_matrix_pencil

Topic: quantum   Node: b7acfe6ac44c

Provenance: helper lemma. step towards sporadic_krawtchouk_range_criterion_subspaces

Existence of a linearly independent matrix pencil of size (k + ℓ) × n of full column rank for all nonzero x ∈ C^m implies the existence of range criterion subspaces D and E of codimensions k and ℓ.
-/

open scoped TensorProduct in

noncomputable def pencilMap (m n k : ℕ) (A : Fin k → Matrix (Fin m) (Fin n) ℂ) :
    TensorProduct ℂ (Fin m → ℂ) (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun (x : Fin m → ℂ) (y : Fin n → ℂ) (i : Fin k) =>
      ∑ r : Fin m, ∑ s : Fin n, x r * A i r s * y s)
    (by intro x x' y; ext i; simp [add_mul, Finset.sum_add_distrib])
    (by intro c x y; ext i; simp [Finset.mul_sum, mul_assoc])
    (by intro x y y'; ext i; simp [mul_add, Finset.sum_add_distrib])
    (by intro c x y; ext i; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring))

open scoped TensorProduct in
lemma pencilMap_tmul (m n k : ℕ) (A : Fin k → Matrix (Fin m) (Fin n) ℂ) (x : Fin m → ℂ) (y : Fin n → ℂ)
    (i : Fin k) : pencilMap m n k A (x ⊗ₜ[ℂ] y) i = ∑ r : Fin m, ∑ s : Fin n, x r * A i r s * y s := by
  simp [pencilMap]

open scoped TensorProduct in
lemma pencilMap_surjective (m n k : ℕ) (A : Fin k → Matrix (Fin m) (Fin n) ℂ)
    (hA : LinearIndependent ℂ A) : Function.Surjective (pencilMap m n k A) := by
  classical
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set c : Fin k → ℂ := fun i => f (Pi.single i 1)
  have hfc : ∀ v : Fin k → ℂ, f v = ∑ i, c i * v i := by
    intro v
    have hv : v = ∑ i, v i • (Pi.single i (1 : ℂ) : Fin k → ℂ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, c, mul_comm]
  have hzero : ∑ i, c i • A i = 0 := by
    ext r s
    have := hf (LinearMap.mem_range_self (pencilMap m n k A) (Pi.single r 1 ⊗ₜ[ℂ] Pi.single s 1))
    rw [LinearMap.mem_ker, hfc] at this
    simp only [pencilMap_tmul] at this
    simpa [Matrix.sum_apply, Pi.single_apply, Finset.sum_ite_eq] using this
  have hc := (Fintype.linearIndependent_iff.mp hA) c hzero
  apply hf0
  ext v
  simp [hfc, hc]

open scoped BigOperators in
/-- Existence of a linearly independent matrix pencil of size (k + ℓ) × n of full column rank for all nonzero x ∈ C^m implies the existence of range criterion subspaces D and E of codimensions k and ℓ. -/
theorem has_range_criterion_of_matrix_pencil
    (m n k ℓ : ℕ)
    (A : Fin k → Matrix (Fin m) (Fin n) ℂ)
    (B : Fin ℓ → Matrix (Fin m) (Fin n) ℂ)
    (hA : LinearIndependent ℂ A)
    (hB : LinearIndependent ℂ B)
    (hcond : ∀ (x : Fin m → ℂ) (y : Fin n → ℂ),
      (∀ i : Fin k, ∑ r : Fin m, ∑ s : Fin n, x r * A i r s * y s = 0) →
      (∀ j : Fin ℓ, ∑ r : Fin m, ∑ s : Fin n, star (x r) * B j r s * y s = 0) →
      x = 0 ∨ y = 0) :
    has_range_criterion_subspaces m n k ℓ := by
  refine ⟨LinearMap.ker (pencilMap m n k A), LinearMap.ker (pencilMap m n ℓ B), ?_, ?_, ?_⟩
  · rw [(LinearMap.quotKerEquivOfSurjective _ (pencilMap_surjective m n k A hA)).finrank_eq]
    simp
  · rw [(LinearMap.quotKerEquivOfSurjective _ (pencilMap_surjective m n ℓ B hB)).finrank_eq]
    simp
  · intro x y hx hy
    apply hcond x y
    · intro i
      have := congrFun (LinearMap.mem_ker.mp hx) i
      simpa [pencilMap_tmul] using this
    · intro j
      have := congrFun (LinearMap.mem_ker.mp hy) j
      simpa [pencilMap_tmul] using this
