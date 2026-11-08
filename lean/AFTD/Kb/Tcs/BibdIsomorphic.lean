import AFTD.Prelude
import AFTD.Kb.Tcs.BIBD

/-!
# bibd_isomorphic

Topic: graphs   Node: 90330c3295f8

Provenance: formalization of a published result. Source: arXiv:2611.05762 Sec. 6.30

Two balanced incomplete block designs D₁ and D₂ with parameters (v, b, r, k, λ) are isomorphic if there exist a bijection f between their point sets and a bijection g between their block sets such that for every block b₁ and point x, x is in block b₁ in D₁ if and only if f(x) is in block g(b₁) in D₂.
-/

/-- Isomorphism between two balanced incomplete block designs with parameters (v, b, r, k, λ). -/
def bibd_isomorphic {X₁ B₁ X₂ B₂ : Type*} {v b r k lam : ℕ}
    (D₁ : BIBD X₁ B₁ v b r k lam) (D₂ : BIBD X₂ B₂ v b r k lam) : Prop := ∃ (f : X₁ ≃ X₂) (g : B₁ ≃ B₂),
    ∀ (b₁ : B₁) (x : X₁), (∃ j : Fin k, D₁.block_pts b₁ j = x) ↔ (∃ j' : Fin k, D₂.block_pts (g b₁) j' = f x)
