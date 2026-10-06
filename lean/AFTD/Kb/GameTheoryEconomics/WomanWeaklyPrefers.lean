import AFTD.Prelude

/-!
# woman_weakly_prefers

Topic: matching_markets   Node: c99195b0c6f8

Provenance: formalization of a published result. Source: College Admissions and the Stability of Marriage (1962), men-proposing deferred acceptance; It's Not All Black and White: Degree of Truthfulness for Risk-Avoiding Agents, arXiv:2502.18805 v3, Def. 3.1 and Sec. 8.1

Under a woman's true ranking (unmatched worst), outcome a is at least as good as outcome b.
-/

/-- Woman's view of two outcomes under her true ranking `T` (0 = best, unmatched worst): `a` is at least as good as `b`. -/
def woman_weakly_prefers {nm : ℕ} (T : Fin nm → Fin nm) (a b : Option (Fin nm)) : Prop :=
  ∀ y ∈ b, ∃ x ∈ a, T x ≤ T y
