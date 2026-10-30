import AFTD.Prelude

/-!
# icosahedron_cartesian_power_diameter_bound_exceeded

Topic: graphs   Node: 312a43b86af5

Provenance: helper lemma. arXiv:2610.36620, Proof of Theorem 3.6

For every integer m ≥ 2, the quantity 2 * (5 * m) / (2 + 2) is strictly less than 3 * m.
-/

/-- For m ≥ 2, 2 * (5 * m) / (2 + 2) < 3 * m. -/
theorem icosahedron_cartesian_power_diameter_bound_exceeded (m : ℕ) (hm : 2 ≤ m) :
    2 * (5 * m) / (2 + 2) < 3 * m := by
  omega
