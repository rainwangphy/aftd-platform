import AFTD.Prelude

/-!
# is_add_involution

Topic: combinatorics   Node: 26c0fee99a42

Provenance: formalization of a published result. Source: arXiv:2611.18059:104-106

An element h in an additive Abelian group is an involution if h ≠ 0 and 2h = 0.
-/

/-- An involution in an additive Abelian group is a non-identity element whose double is zero. -/
def is_add_involution {Γ : Type*} [AddCommGroup Γ] (h : Γ) : Prop :=
  h ≠ 0 ∧ h + h = 0
