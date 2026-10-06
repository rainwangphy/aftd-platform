import AFTD.Prelude
import AFTD.Kb.Tcs.LineSyndrome
import AFTD.Kb.Tcs.IsotropicSubspaceLowerBound
import AFTD.Kb.Tcs.LineCubicParityReprNonempty
import AFTD.Kb.Tcs.LineCubicParityReprOrtho
import AFTD.Kb.Tcs.LineCubicParityReprEvalZero
import AFTD.Kb.Tcs.IsParityRepr

/-!
# line_cubic_t_count_lower_bound

Topic: quantum   Node: 84e566272d9a

Provenance: formalization of a published result. Source: arXiv:2610.01024, Proposition 65

For any n ≥ 5, every parity representation of the line cubic syndrome has cardinality at least 2n + 1.
-/

/-- Proposition 65 floor: every parity representation of the line cubic syndrome has at least 2n + 1 parities for n ≥ 5. -/
theorem line_cubic_t_count_lower_bound (n : ℕ) (hn : 5 ≤ n) (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (line_syndrome n)) : 2 * n + 1 ≤ S.card := by
  let evalMap : (Fin n → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2) := {
    toFun := fun c y => ∑ j ∈ (y : Finset (Fin n)), c j
    map_add' := by
      intro c d
      ext ⟨y, hy⟩
      dsimp
      rw [← Finset.sum_add_distrib]
    map_smul' := by
      intro a c
      ext ⟨y, hy⟩
      dsimp
      exact (Finset.mul_sum _ _ _).symm
  }
  let V : Submodule (ZMod 2) (S → ZMod 2) := LinearMap.range evalMap
  have h_iso : ∀ u ∈ V, ∀ v ∈ V, (∑ m, u m * v m) = 0 := by
    rintro u ⟨c, rfl⟩ v ⟨d, rfl⟩
    have h1 : (∑ m : S, evalMap c m * evalMap d m) =
              ∑ y ∈ S, (∑ j ∈ y, c j) * (∑ k ∈ y, d k) :=
      Finset.sum_coe_sort S (fun y => (∑ j ∈ y, c j) * (∑ k ∈ y, d k))
    rw [h1]
    exact (line_cubic_parity_repr_ortho n S hS c d).1
  have h_ones_ortho : ∀ v ∈ V, ∑ m, v m = 0 := by
    rintro v ⟨c, rfl⟩
    have h1 : (∑ m : S, evalMap c m) = ∑ y ∈ S, ∑ j ∈ y, c j :=
      Finset.sum_coe_sort S (fun y => ∑ j ∈ y, c j)
    rw [h1]
    exact (line_cubic_parity_repr_ortho n S hS c 0).2
  have h_ones_notin : (fun _ : S => (1 : ZMod 2)) ∉ V := by
    intro ⟨c, hc⟩
    have h_eval : ∀ y ∈ S, ∑ j ∈ y, c j = 1 := by
      intro y hy
      exact congr_fun hc ⟨y, hy⟩
    have hc0 : c = 0 := line_cubic_parity_repr_eval_zero n hn S hS c 1 h_eval
    obtain ⟨y, hy⟩ := line_cubic_parity_repr_nonempty n hn S hS
    have h1 := congr_fun hc ⟨y, hy⟩
    dsimp [evalMap] at h1
    rw [hc0] at h1
    simp only [Pi.zero_apply, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have h_inj : Function.Injective evalMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : ∀ y ∈ S, ∑ j ∈ y, c j = 0 := by
      intro y hy
      exact congr_fun hc ⟨y, hy⟩
    exact line_cubic_parity_repr_eval_zero n hn S hS c 0 h1
  have h_rank : Module.finrank (ZMod 2) V = n := by
    rw [LinearMap.finrank_range_of_inj h_inj]
    simp
  have h_bound := isotropic_subspace_lower_bound V h_iso h_ones_ortho h_ones_notin
  rw [h_rank] at h_bound
  have h_card : Fintype.card S = S.card := by simp
  rwa [h_card] at h_bound
