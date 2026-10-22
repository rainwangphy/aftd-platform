import AFTD.Prelude

/-!
# recursive_line_hole_budget

Topic: combinatorics   Node: 3ff0f5de6f29

Provenance: formalization of a published result. Source: scout/2610-22875-overtake-and-the-recursive-line-equality-for-second-order-z.md:541

The recursive-line hole budget recursive_line_hole_budget m n z z_RL for natural numbers m, n and integers z, z_RL is defined as (m : ℤ) * n + z - 2 * z_RL.
-/

/-- The recursive-line hole budget h_RL(m,n) = mn + z(m,n) - 2 * z_RL(m,n). -/
def recursive_line_hole_budget (m n : ℕ) (z z_RL : ℤ) : ℤ := (m : ℤ) * n + z - 2 * z_RL
