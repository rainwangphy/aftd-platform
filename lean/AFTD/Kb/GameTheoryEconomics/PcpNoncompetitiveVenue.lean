import AFTD.Prelude

/-!
# pcp_noncompetitive_venue

Topic: equilibria   Node: a8c5b2feaa37

Assumption 2 (non-competitive venue): the least competitive venue has the same publication cost for every type.
-/

/-- Assumption 2 (Non-competitive venue) of Wang–Wu–Xu: the least competitive venue (index 0) costs the same for every type. -/
def pcp_noncompetitive_venue {n k : ℕ} (c : Fin n → Fin k → ℝ) : Prop :=
  ∀ (i i' : Fin n) (j : Fin k), j.val = 0 → c i j = c i' j
