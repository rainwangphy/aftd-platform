import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PowerRelation

/-!
# PowerProfile

Topic: social_choice   Node: 0bb9889d478f

Provenance: formalization of a published result. Source: arXiv:2611.19021 Section 2.1

A power profile is a finite multiset of power relations.
-/

/-- A profile of power relations is a multiset of power relations. -/
abbrev PowerProfile (X : Type*) : Type _ := Multiset (PowerRelation X)
