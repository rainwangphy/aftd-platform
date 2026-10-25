import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TraceSplitReconstruction

/-!
# matrix3_trace_saturation

Topic: algebraic_complexity   Node: 7bcf2bf3387b

Provenance: formalization of a published result. Source: arXiv:2610.11823v3, Section 4.2, equation (4.2) with excess zero. The proof here uses the injectivity of the split factor map at equal dimensions and applies over every field; no computational certificates are assumed.

If a cyclic trace decomposition over a field has first-factor matrix ranks summing to 27, then a_t * b_s * c_t * a_s equals a_s for t=s and zero otherwise.
-/

open Matrix Finset
noncomputable section
variable {K : Type*} [Field K] {r : ℕ}

private abbrev matrix3_saturation_space (a : Fin r → Matrix (Fin 3) (Fin 3) K) :=
  ∀ s, LinearMap.range (a s).mulVecLin

private def matrix3_saturation_map (a b : Fin r → Matrix (Fin 3) (Fin 3) K) :
    matrix3_saturation_space a →ₗ[K] (Fin 3 × Fin 3 × Fin 3 → K) where
  toFun x p := ∑ s, (x s).val p.1 * b s p.2.1 p.2.2
  map_add' x y := by
    ext p
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    ext p
    simp [Finset.mul_sum, mul_assoc]

private def matrix3_saturation_preimage (a c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (z : Fin 3 × Fin 3 × Fin 3 → K) : matrix3_saturation_space a :=
  fun s => ⟨(a s).mulVecLin (fun j => ∑ k, ∑ i, c s k i * z (i,j,k)),
    ⟨_, rfl⟩⟩

private theorem matrix3_saturation_reconstruction (a b c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0)
    (z : Fin 3 × Fin 3 × Fin 3 → K) :
    matrix3_saturation_map a b (matrix3_saturation_preimage a c z) = z := by
  ext p
  exact matrix3_trace_split_reconstruction a b c h z p
end

theorem matrix3_trace_saturation {K : Type*} [Field K] {r : ℕ} (a b c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0)
    (hd : ∑ s, (a s).rank = 27) :
    ∀ t s, a t * b s * c t * a s = if t = s then a s else 0 := by
  classical
  have hdim : Module.finrank K (matrix3_saturation_space a) =
      Module.finrank K (Fin 3 × Fin 3 × Fin 3 → K) := by
    simpa [matrix3_saturation_space, Module.finrank_pi, Module.finrank_pi_fintype, Matrix.rank] using hd
  have hinj : Function.Injective (matrix3_saturation_map a b) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
      (fun z => ⟨matrix3_saturation_preimage a c z, matrix3_saturation_reconstruction a b c h z⟩)
  have hyx (x : matrix3_saturation_space a) : matrix3_saturation_preimage a c (matrix3_saturation_map a b x) = x := by
    apply hinj
    exact matrix3_saturation_reconstruction a b c h _
  intro t s
  ext i j
  let v : LinearMap.range (a s).mulVecLin :=
    ⟨(a s).col j, ⟨Pi.single j 1, by simp⟩⟩
  have hv := congrArg (fun x : matrix3_saturation_space a => (x t).val i) (hyx (Pi.single s v))
  have hsimp : ∀ p, (matrix3_saturation_map a b (Pi.single s v)) p =
      a s p.1 j * b s p.2.1 p.2.2 := by
    intro p
    change (∑ q, ((Pi.single s v : matrix3_saturation_space a) q).val p.1 * b q p.2.1 p.2.2) = _
    rw [Finset.sum_eq_single s]
    · simp [v]
    · intro q _ hqs
      simp [Pi.single_eq_of_ne hqs]
    · simp
  simp only [matrix3_saturation_preimage, mulVecLin_apply,
    mulVec, dotProduct, hsimp] at hv
  have hexpand : (a t * b s * c t * a s) i j =
      ∑ q, a t i q * (∑ k, ∑ i', c t k i' * (a s i' j * b s q k)) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [hexpand, hv]
  by_cases hts : t = s
  · subst t
    simp [v]
  · simp [hts, v]
