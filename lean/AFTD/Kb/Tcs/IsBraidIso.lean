import AFTD.Prelude

/-!
# is_braid_iso

Topic: combinatorics   Node: d6184e7859fd

Provenance: formalization of a published result. Source: scout/2611-15540-solutions-of-the-set-theoretic-quantum-yang-baxter-equation.md:147

Two maps R : X × X → X × X and S : Y × Y → Y × Y are isomorphic if there exists an equivalence e : X ≃ Y such that (e × e) ∘ R = S ∘ (e × e).
-/

/-- Isomorphism between two braid maps, witnessed by an equivalence intertwining them. -/
def is_braid_iso {X Y : Type*} (R : X × X → X × X) (S : Y × Y → Y × Y) : Prop :=
  ∃ e : X ≃ Y, Prod.map e e ∘ R = S ∘ Prod.map e e
