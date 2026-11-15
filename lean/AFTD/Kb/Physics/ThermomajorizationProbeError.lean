import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationDiff

/-!
# thermomajorization_probe_error

Topic: quantum_mechanics   Node: ae5d10b50802

Provenance: formalization of a published result. Source: arXiv:2610.35433

For population vectors x, y : Fin n → ℝ and a finite set of probe ranks F : Finset ℕ, the detected conversion error thermomajorization_probe_error n F x y is the maximum of {0} ∪ {thermomajorization_diff x y j : j ∈ F}.
-/

/-- Detected thermomajorization conversion error for a set of binary probe ranks. -/
noncomputable def thermomajorization_probe_error (n : ℕ) (F : Finset ℕ) (x y : Fin n → ℝ) : ℝ := (insert (0 : ℝ) (F.image (thermomajorization_diff x y))).max' (Finset.insert_nonempty 0 _)
