import AFTD.Prelude
import AFTD.Kb.Optimization.HypercubeCoordReflect
import AFTD.Kb.Optimization.HypercubeMaj

/-!
# hypercube_coord_reflect_maj

Topic: submodular   Node: 0b36c68656ba

Provenance: helper lemma. arXiv:2610.38287 Proof of Theorem 2

For any coordinate subset T of Fin n and any Boolean vectors x, y, z : Fin n → Bool, the coordinate reflection of their componentwise majority equals the componentwise majority of their coordinate reflections.
-/

/-- Coordinate reflection commutes with the majority operation on Boolean vectors. -/
theorem hypercube_coord_reflect_maj {n : ℕ} (T : Finset (Fin n)) (x y z : Fin n → Bool) :
    hypercube_coord_reflect T (hypercube_maj x y z) =
      hypercube_maj (hypercube_coord_reflect T x) (hypercube_coord_reflect T y) (hypercube_coord_reflect T z) := by
  ext i
  simp only [hypercube_coord_reflect, hypercube_maj, Pi.inf_apply, Pi.sup_apply]
  split_ifs
  · cases x i <;> cases y i <;> cases z i <;> rfl
  · rfl
