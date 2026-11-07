import AFTD.Prelude

/-!
# cyclic_has_copy

Topic: graphs   Node: d1593e361b56

Provenance: formalization of a published result. Source: arXiv:2611.08375, Sec. 1

A cyclically ordered graph G on Fin N contains a cyclically ordered copy of H on Fin m if there is an injective graph homomorphism from H to G preserving strict cyclic betweenness sbtw.
-/

/-- Existence of a cyclic order-preserving subgraph embedding. -/
def cyclic_has_copy {m N : ℕ} (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin N)) : Prop := ∃ f : Fin m → Fin N,
    Function.Injective f ∧
    (∀ ⦃u v : Fin m⦄, H.Adj u v → G.Adj (f u) (f v)) ∧
    (∀ ⦃u v w : Fin m⦄, sbtw u v w → sbtw (f u) (f v) (f w))
