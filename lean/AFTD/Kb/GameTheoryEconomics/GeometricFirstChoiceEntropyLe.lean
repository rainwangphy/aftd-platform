import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GeometricStepEntropyLe

/-!
# geometric_first_choice_entropy_le

Topic: social_choice   Node: 1f7422e52e6a

For geometric weights phi^a and any nonempty set S of alternatives, the entropy of the first choice is at most log(1/(1-phi)) + log(1/phi) * phi/(1-phi)^2 (shift exponents by the minimum).
-/

/-- The first-choice entropy of the geometric Plackett–Luce model on any nonempty `S ⊆ ℕ`. -/
lemma geometric_first_choice_entropy_le (φ : ℝ) (h0 : 0 < φ) (h1 : φ < 1) (S : Finset ℕ)
    (hS : S.Nonempty) :
    ∑ a ∈ S, Real.negMulLog (φ ^ a / ∑ b ∈ S, φ ^ b) ≤
      Real.log (1 - φ)⁻¹ + (-Real.log φ) * (φ / (1 - φ) ^ 2) := by
  set t := S.min' hS
  have ht : ∀ a ∈ S, t ≤ a := fun a ha => S.min'_le a ha
  have hinj : Set.InjOn (fun a => a - t) S := by
    intro x hx y hy h; simp only at h; have := ht x hx; have := ht y hy; omega
  have hsplit : ∀ a ∈ S, φ ^ a = φ ^ t * φ ^ (a - t) := fun a ha => by
    rw [← pow_add, Nat.add_sub_cancel' (ht a ha)]
  have hZ : ∑ b ∈ S, φ ^ b = φ ^ t * ∑ k ∈ S.image (fun a => a - t), φ ^ k := by
    rw [Finset.sum_image hinj, Finset.mul_sum]; exact Finset.sum_congr rfl hsplit
  have hpt : 0 < φ ^ t := pow_pos h0 t
  calc ∑ a ∈ S, Real.negMulLog (φ ^ a / ∑ b ∈ S, φ ^ b)
      = ∑ k ∈ S.image (fun a => a - t),
          Real.negMulLog (φ ^ k / ∑ j ∈ S.image (fun a => a - t), φ ^ j) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [hZ, hsplit a ha, mul_div_mul_left _ _ hpt.ne']
    _ ≤ _ := geometric_step_entropy_le φ h0 h1 _
        (Finset.mem_image.2 ⟨t, S.min'_mem hS, Nat.sub_self t⟩)
