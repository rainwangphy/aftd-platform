import AFTD.Prelude
import AFTD.Kb.Tcs.IsSunflower

/-!
# isSunflower_core_unique

Topic: combinatorics   Node: b25c20a76546

If a finite family F of finite sets has at least two members and is a sunflower with kernel C and also a sunflower with kernel C', then C = C'.
-/

/-- The kernel of a sunflower with at least two members is unique. -/
theorem isSunflower_core_unique {α : Type*} [DecidableEq α] {F : Finset (Finset α)} {C C' : Finset α}
    (h : IsSunflower F C) (h' : IsSunflower F C') (hF : 2 ≤ F.card) : C = C' := by
  have hF' : 1 < F.card := by omega
  rw [Finset.one_lt_card] at hF'
  obtain ⟨A, hA, B, hB, hAB⟩ := hF'
  rw [IsSunflower] at h h'
  rw [← h.2 A hA B hB hAB, ← h'.2 A hA B hB hAB]
