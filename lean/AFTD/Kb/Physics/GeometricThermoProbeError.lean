import AFTD.Prelude
import AFTD.Kb.Physics.GeometricThermoDiff

/-!
# geometric_thermo_probe_error

Topic: quantum_mechanics   Node: 2575d95d9ec6

Provenance: formalization of a published result. Source: arXiv:2610.35433

For dimension N, parameter q, probe set F : Finset ℕ, and population vectors x, y : Fin N → ℝ, the detected probe error geometric_thermo_probe_error N q F x y is the maximum of the finite set {0} ∪ {geometric_thermo_diff N q x y j : j ∈ F}.
-/

/-- Maximum thermomajorization discrepancy detected by probe set F. -/
noncomputable def geometric_thermo_probe_error (N : ℕ) (q : ℝ) (F : Finset ℕ) (x y : Fin N → ℝ) : ℝ := (insert (0 : ℝ) (F.image (geometric_thermo_diff N q x y))).max' (Finset.insert_nonempty 0 _)
