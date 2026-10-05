import AFTD.Prelude

/-!
# team_v

Topic: algorithms   Node: ee0a9592af27

Column potentials of a dual certificate for the maximum-weight matching.
-/

/-- Column potentials of a dual certificate for the maximum-weight matching. -/
noncomputable def team_v {m : ℕ} (j : Fin (2 * m + 3)) : ℝ :=
  if j.val = 0 then 0 else if j.val = 1 then 1 / 4 else if j.val % 2 = 0 then 1 / 2 else 0
