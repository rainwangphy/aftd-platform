import AFTD.Prelude

/-!
# deterministic_menu

Topic: mechanism_design   Node: abea9bd270ff

Provenance: formalization of a published result. Source: arXiv:2611.33095 Section 2.1

A deterministic menu on a type E is a set of dependent pairs ⟨S, x_S⟩ where S : Finset E is a finite subset of items and x_S : S → ℝ is the principal value vector on S.
-/

/-- A deterministic menu is a set of dependent pairs (S, x_S) of finite sets and principal value vectors. -/
abbrev deterministic_menu (E : Type*) := Set ((S : Finset E) × (S → ℝ))
