import AFTD.Prelude
import AFTD.Kb.Tcs.IsSunflower

/-!
# isSunflower_mono

Topic: combinatorics   Node: dc2edbb01022

A subfamily of a sunflower is again a sunflower with the same kernel: if G ⊆ F and F is a sunflower with kernel C, then every member of G contains C and any two distinct members of G intersect in exactly C, so G is a sunflower with kernel C.
-/

/-- A subfamily of a sunflower with kernel C is a sunflower with kernel C. -/
theorem isSunflower_mono {α : Type*} [DecidableEq α] {F G : Finset (Finset α)} {C : Finset α}
    (hGF : G ⊆ F) (h : IsSunflower F C) : IsSunflower G C := by
  rw [IsSunflower] at h ⊢
  exact ⟨fun A hA => h.1 A (hGF hA), fun A hA B hB hne => h.2 A (hGF hA) B (hGF hB) hne⟩
