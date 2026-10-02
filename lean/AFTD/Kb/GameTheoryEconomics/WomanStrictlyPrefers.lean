import AFTD.Prelude

/-!
# woman_strictly_prefers

Topic: matching_markets   Node: ecaadc12096f

Under a woman's true ranking (unmatched worst), outcome a is strictly better than outcome b.
-/

/-- Woman's view of two outcomes under her true ranking `T` (0 = best, unmatched worst): `a` is strictly better than `b`. -/
def woman_strictly_prefers {nm : ℕ} (T : Fin nm → Fin nm) (a b : Option (Fin nm)) : Prop :=
  ∃ x ∈ a, ∀ y ∈ b, T x < T y
