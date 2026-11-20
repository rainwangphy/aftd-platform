import AFTD.Prelude
import AFTD.Kb.NumberTheory.DavenportConstant

/-!
# group_davenport_constant

Topic: combinatorics   Node: 8dc8a490a874

Provenance: formalization of a published result. Source: arXiv:2611.20197, Section 1

The Davenport constant D(G) of an additive abelian group G is the natural number obtained from the supremum of the lengths of minimal zero-sum sequences over G.
-/

/-- The Davenport constant of an additive commutative group, taking values in ℕ. -/
noncomputable def group_davenport_constant (G : Type*) [AddCommGroup G] : ℕ := (davenport_constant (Set.univ : Set G)).toNat
