import AFTD.Prelude
import AFTD.Kb.Optimization.HypercubeCoordReflect

/-!
# hypercube_coord_reflect_involutive

Topic: submodular   Node: beeb2b894b69

Provenance: helper lemma. arXiv:2610.38287 Eq. (14)

For any coordinate subset T of Fin n and any Boolean vector x : Fin n → Bool, applying coordinate reflection with respect to T twice returns x.
-/

/-- Coordinate reflection on the unit hypercube is an involution. -/
theorem hypercube_coord_reflect_involutive {n : ℕ} (T : Finset (Fin n)) (x : Fin n → Bool) :
    hypercube_coord_reflect T (hypercube_coord_reflect T x) = x := by
  ext i
  simp [hypercube_coord_reflect]
  split_ifs <;> simp
