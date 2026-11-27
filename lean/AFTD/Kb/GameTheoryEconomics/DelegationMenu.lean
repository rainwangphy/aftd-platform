import AFTD.Prelude

/-!
# DelegationMenu

Topic: mechanism_design   Node: 04c08cfe7259

Provenance: formalization of a published result. Source: arXiv:2611.33095 Section 2.1

A delegation menu on a type E consists of an acceptance predicate accepts : Finset E → (E → ℝ) → Prop indicating whether a finite subset S is accepted given principal values x : E → ℝ.
-/

/-- A delegation menu on items E specifies an acceptance predicate for each report and principal values. -/
structure DelegationMenu (E : Type*) where
  accepts : Finset E → (E → ℝ) → Prop
