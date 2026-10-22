import AFTD.Prelude

/-!
# k_submod_le

Topic: submodular   Node: 345da4118212

Provenance: formalization of a published result. Source: arXiv:2610.26677, line 106

Componentwise partial order on assignments Fin n → Option (Fin k), where x ≤ y if for every element e, x e = none or x e = y e.
-/

/-- Componentwise partial order on assignments Fin n → Option (Fin k). -/
def k_submod_le {n k : ℕ} (x y : Fin n → Option (Fin k)) : Prop := ∀ e, x e = none ∨ x e = y e
