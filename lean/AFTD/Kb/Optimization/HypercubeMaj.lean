import AFTD.Prelude

/-!
# hypercube_maj

Topic: submodular   Node: a9e53b01b059

Provenance: formalization of a published result. Source: arXiv:2610.38287 Section 2.3.1

Given three Boolean vectors x, y, z : Fin n → Bool, hypercube_maj x y z is their componentwise majority vector, defined by (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x).
-/

/-- Componentwise majority vector of three Boolean vectors. -/
def hypercube_maj {n : ℕ} (x y z : Fin n → Bool) : Fin n → Bool := (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x)
