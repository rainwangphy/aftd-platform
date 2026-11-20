import AFTD.Prelude
import AFTD.Kb.Tcs.CraigShellSize

/-!
# craig_shell_size_three_one

Topic: information   Node: ce18bda13ee4

Provenance: formalization of a published result. Source: arXiv:2611.22441 Eq. (7)

For p = 3 and k = 1, the shortest vector shell size of Craig's lattice is 6.
-/

/-- The shortest vector shell size in Craig's lattice for p = 3 and k = 1 is 6. -/
theorem craig_shell_size_three_one : craig_shell_size 3 1 = 6 := rfl
