import AFTD.Prelude
import AFTD.Kb.Tcs.IsSunflower

/-!
# isSunflower_empty_core_iff_pairwise_disjoint

Topic: combinatorics   Node: 2c15c4fcf018

A finite family F of finite sets is a sunflower with empty kernel if and only if its members are pairwise disjoint.
-/

/-- A family is a sunflower with empty kernel iff its members are pairwise disjoint. -/
theorem isSunflower_empty_core_iff_pairwise_disjoint {α : Type*} [DecidableEq α] (F : Finset (Finset α)) :
    IsSunflower F ∅ ↔ ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B := by
  simp [IsSunflower, Finset.disjoint_iff_inter_eq_empty]
