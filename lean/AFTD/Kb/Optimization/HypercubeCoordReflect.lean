import AFTD.Prelude

/-!
# hypercube_coord_reflect

Topic: submodular   Node: f06f272411d6

Provenance: formalization of a published result. Source: arXiv:2610.38287 Eq. (14)

Given a coordinate subset T of Fin n and a Boolean vector x : Fin n → Bool, hypercube_coord_reflect T x is the Boolean vector obtained by negating the coordinate x i if i ∈ T and leaving it unchanged otherwise.
-/

/-- Coordinate reflection of a Boolean vector on Fin n with respect to a coordinate subset T. -/
def hypercube_coord_reflect {n : ℕ} (T : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool := fun i => if i ∈ T then !x i else x i
