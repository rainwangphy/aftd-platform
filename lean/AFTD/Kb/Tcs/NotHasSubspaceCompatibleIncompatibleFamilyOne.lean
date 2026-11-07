import AFTD.Prelude
import AFTD.Kb.Tcs.HasSubspaceCompatibleIncompatibleFamily

/-!
# not_has_subspace_compatible_incompatible_family_one

Topic: quantum   Node: cc33d8b00ac0

Provenance: helper lemma. arXiv:2610.37347 (Measurement incompatibility and noiseless quantum codes), after Corollary 1

For any dimension d, no single binary measurement can be incompatible on C^d, so has_subspace_compatible_incompatible_family d 1 does not hold.
-/

private lemma not_has_subspace_compatible_incompatible_family_one_sum_fin_one_bool
    {M : Type*} [AddCommMonoid M] (f : (Fin 1 → Bool) → M) :
    (∑ s : Fin 1 → Bool, f s) = f (fun _ => true) + f (fun _ => false) := by
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) Bool).symm f]
  simp only [Equiv.funUnique_symm_apply]
  rw [Fintype.univ_bool, Finset.sum_pair (by decide)]
  congr 2

/-- A single binary measurement is always jointly measurable, so no 1-measurement family can be incompatible globally. -/
theorem not_has_subspace_compatible_incompatible_family_one (d : ℕ) : ¬ has_subspace_compatible_incompatible_family d 1 := by
  rintro ⟨M, hM, hinc, -⟩
  apply hinc
  refine ⟨fun s => if s 0 = true then M 0 else 1 - M 0, ?_, ?_, ?_⟩
  · intro s
    by_cases h : s 0 = true
    · simp only [h, if_true]; exact (hM 0).1
    · simp only [h]; exact (hM 0).2
  · rw [not_has_subspace_compatible_incompatible_family_one_sum_fin_one_bool]
    simp
  · intro j
    fin_cases j
    rw [not_has_subspace_compatible_incompatible_family_one_sum_fin_one_bool]
    simp
