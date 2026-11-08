import AFTD.Prelude
import AFTD.Kb.Optimization.HypercubeCoordReflect

/-!
# hypercube_reflected_join

Topic: submodular   Node: f49a6cb4933f

Provenance: formalization of a published result. Source: arXiv:2610.38287 Eq. (15)

Given a coordinate subset T of Fin n and Boolean vectors x and y, hypercube_reflected_join T x y is the reflected join of x and y with respect to T, defined by hypercube_coord_reflect T (hypercube_coord_reflect T x ⊔ hypercube_coord_reflect T y).
-/

/-- Reflected join of two Boolean vectors with respect to a coordinate subset T. -/
def hypercube_reflected_join {n : ℕ} (T : Finset (Fin n)) (x y : Fin n → Bool) : Fin n → Bool := hypercube_coord_reflect T (hypercube_coord_reflect T x ⊔ hypercube_coord_reflect T y)
