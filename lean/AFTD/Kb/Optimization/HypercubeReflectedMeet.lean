import AFTD.Prelude
import AFTD.Kb.Optimization.HypercubeCoordReflect

/-!
# hypercube_reflected_meet

Topic: submodular   Node: 27653d95e30a

Provenance: formalization of a published result. Source: arXiv:2610.38287 Eq. (15)

Given a coordinate subset T of Fin n and Boolean vectors x and y, hypercube_reflected_meet T x y is the reflected meet of x and y with respect to T, defined by hypercube_coord_reflect T (hypercube_coord_reflect T x ⊓ hypercube_coord_reflect T y).
-/

/-- Reflected meet of two Boolean vectors with respect to a coordinate subset T. -/
def hypercube_reflected_meet {n : ℕ} (T : Finset (Fin n)) (x y : Fin n → Bool) : Fin n → Bool := hypercube_coord_reflect T (hypercube_coord_reflect T x ⊓ hypercube_coord_reflect T y)
