import AFTD.Prelude

/-!
# woman_weakly_prefers

Topic: matching_markets   Node: c99195b0c6f8

Under a woman's true ranking (unmatched worst), outcome a is at least as good as outcome b.
-/

/-- Woman's view of two outcomes under her true ranking `T` (0 = best, unmatched worst): `a` is at least as good as `b`. -/
def woman_weakly_prefers {nm : ℕ} (T : Fin nm → Fin nm) (a b : Option (Fin nm)) : Prop :=
  ∀ y ∈ b, ∃ x ∈ a, T x ≤ T y
