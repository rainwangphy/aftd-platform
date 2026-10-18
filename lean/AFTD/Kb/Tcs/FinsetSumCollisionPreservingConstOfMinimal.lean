import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetSumCollisionPreserving
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsMaxLayer
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# finset_sum_collision_preserving_const_of_minimal

Topic: combinatorics   Node: 0fa425725665

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

If A is NUS, no proper subset of A is NUS (A is inclusion-minimal), and x is a rational collision-preserving weight on A, then x is constant on A.
-/

/-- Lemma 2.1 (rational half) of arXiv:2610.09349: a collision-preserving rational weight on an inclusion-minimal NUS set is constant. -/
theorem finset_sum_collision_preserving_const_of_minimal {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {A : Finset G} (hA : finset_has_no_unique_sums A)
    (hmin : ∀ B : Finset G, B ⊂ A → ¬ finset_has_no_unique_sums B)
    {x : G → ℚ} (hx : finset_sum_collision_preserving A x) :
    ∀ a ∈ A, ∀ b ∈ A, x a = x b := by
  have hne : A.Nonempty := by
    have h := hA.1
    exact Finset.card_pos.mp (by omega)
  obtain ⟨a₀, ha₀, hmax⟩ := Finset.exists_max_image A x hne
  have hNUS : finset_has_no_unique_sums (A.filter (fun a => x a = x a₀)) :=
    finset_has_no_unique_sums_max_layer hA x hx (x a₀) (fun a ha => hmax a ha) ⟨a₀, ha₀, rfl⟩
  have hsub : A.filter (fun a => x a = x a₀) ⊆ A := Finset.filter_subset _ _
  have heq : A.filter (fun a => x a = x a₀) = A := by
    by_contra hne'
    exact hmin _ (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩) hNUS
  intro a ha b hb
  have ha' : x a = x a₀ := by
    have : a ∈ A.filter (fun a => x a = x a₀) := by rw [heq]; exact ha
    exact (Finset.mem_filter.mp this).2
  have hb' : x b = x a₀ := by
    have : b ∈ A.filter (fun a => x a = x a₀) := by rw [heq]; exact hb
    exact (Finset.mem_filter.mp this).2
  rw [ha', hb']
