import AFTD.Prelude
import AFTD.Kb.Optimization.PermGroupSymmetrize
import AFTD.Kb.Optimization.FinsetIndicatorVec
import AFTD.Kb.Optimization.IsStronglySymmetricInstance

/-!
# is_strongly_symmetric_instance_bot

Topic: submodular   Node: 595a9cc5b876

Provenance: helper lemma. step towards matroid_symmetry_gap_lt_eight_seventeenths

Every matroid together with any set function is a strongly symmetric instance for the trivial permutation group: a witness that the definition of strong symmetry is inhabited (non-vacuity).
-/

/-- Non-vacuity witness: with the trivial group, every (M, f) is a strongly symmetric instance. -/
theorem is_strongly_symmetric_instance_bot {m : ℕ} (M : Matroid (Fin m))
    (f : Finset (Fin m) → ℝ) :
    is_strongly_symmetric_instance M f ⊥ := by
  classical
  have hsym : ∀ (y : Fin m → ℝ),
      perm_group_symmetrize (⊥ : Subgroup (Equiv.Perm (Fin m))) y = y := by
    intro y
    funext u
    have h1 : (Finset.univ.filter (fun x : Equiv.Perm (Fin m) =>
        x ∈ (⊥ : Subgroup (Equiv.Perm (Fin m))))) = {1} := by
      ext x; simp [Subgroup.mem_bot]
    rw [perm_group_symmetrize, h1, Finset.sum_singleton, Finset.card_singleton,
      Nat.cast_one, div_one]
    simp
  have hmap : ∀ (S : Finset (Fin m)),
      Finset.map (Equiv.toEmbedding (1 : Equiv.Perm (Fin m))) S = S := by
    intro S
    ext x
    simp only [Finset.mem_map, Equiv.coe_toEmbedding, Equiv.Perm.one_apply]
    simp
  refine ⟨?_, ?_⟩
  · intro σ hσ S
    rw [Subgroup.mem_bot] at hσ
    subst hσ
    rw [hmap]
  · intro S S' h
    rw [hsym, hsym] at h
    have hSS : S = S' := by
      ext u
      have h2 := congrFun h u
      simp only [finset_indicator_vec] at h2
      constructor <;> intro hu
      · by_contra h1
        simp [h1] at h2
        simp [hu] at h2
      · by_contra h1
        simp [h1] at h2
        simp [hu] at h2
    simp [hSS]
