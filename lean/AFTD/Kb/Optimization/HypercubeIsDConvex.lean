import AFTD.Prelude
import AFTD.Kb.Optimization.HypercubeReflectedMeet
import AFTD.Kb.Optimization.HypercubeReflectedJoin

/-!
# hypercube_is_d_convex

Topic: submodular   Node: abea260c9c8a

Provenance: formalization of a published result. Source: arXiv:2610.38287 Eq. (16)

A finite set X of Boolean vectors in Fin n → Bool is D-convex (hypercube_is_d_convex X) if there exists a coordinate subset T of Fin n such that for all x, y ∈ X, both hypercube_reflected_meet T x y and hypercube_reflected_join T x y belong to X.
-/

/-- A set of vertices of the unit hypercube is D-convex if it is closed under the coordinate-reflected meet and join for some coordinate subset T. -/
def hypercube_is_d_convex {n : ℕ} (X : Finset (Fin n → Bool)) : Prop := ∃ T : Finset (Fin n), ∀ x ∈ X, ∀ y ∈ X,
    hypercube_reflected_meet T x y ∈ X ∧ hypercube_reflected_join T x y ∈ X
