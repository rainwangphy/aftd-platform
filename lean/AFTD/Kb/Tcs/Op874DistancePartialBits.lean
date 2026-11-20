import AFTD.Prelude
import AFTD.Kb.Tcs.Op874DistanceParitySuccNe

/-!
# op874_distance_partial_bits

Topic: graphs   Node: 274a8c2ca275

Provenance: helper lemma. A descending-distance certificate yields the required partial bit assignment.

If each nonroot vertex descends in distance to an allowed successor and both specified successors have odd distance, parity gives the needed partial bits.
-/

theorem op874_distance_partial_bits {X : Type*} [DecidableEq X] (p q : X → X) (S : Finset X)
    (r x : X) (d : X → ℕ) (hr : r ∈ S) (hx : x ∈ S) (hp : p x ∈ S) (hq : q x ∈ S)
    (hfix : p x ≠ x ∧ q x ≠ x) (hodd : d (p x) % 2 = 1 ∧ d (q x) % 2 = 1)
    (hdesc : ∀ y ∈ S, y ≠ r → y ≠ x →
      (p y ∈ S ∧ p y ≠ x ∧ d y = d (p y) + 1) ∨
      (q y ∈ S ∧ q y ≠ x ∧ d y = d (q y) + 1)) :
    ∃ b : X → Bool, (∀ y ∈ S, y ≠ r →
      (p y ∈ S ∧ b y ≠ b (p y)) ∨ (q y ∈ S ∧ b y ≠ b (q y))) ∧
      b x ≠ b (p x) ∧ b x ≠ b (q x) := by
  let b : X → Bool := fun y => if y = x then true else decide (d y % 2 = 0)
  have hpx : b x ≠ b (p x) := by simp [b, hfix.1, hodd.1]
  have hqx : b x ≠ b (q x) := by simp [b, hfix.2, hodd.2]
  refine ⟨b, ?_, hpx, hqx⟩
  intro y hy hyr
  by_cases hyx : y = x
  · subst y
    exact Or.inl ⟨hp, hpx⟩
  · rcases hdesc y hy hyr hyx with ⟨hys, hyx', hd⟩ | ⟨hys, hyx', hd⟩
    · left
      refine ⟨hys, ?_⟩
      simp only [b, if_neg hyx, if_neg hyx']
      rw [hd]
      exact op874_distance_parity_succ_ne _
    · right
      refine ⟨hys, ?_⟩
      simp only [b, if_neg hyx, if_neg hyx']
      rw [hd]
      exact op874_distance_parity_succ_ne _
