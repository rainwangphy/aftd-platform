import AFTD.Prelude
import AFTD.Kb.Tcs.Biplane

/-!
# BiplaneFlag

Topic: combinatorics   Node: fef08e3570b1

Provenance: formalization of a published result. Source: arXiv:2611.17855, Section 2.2

The type of flags of a biplane, defined as pairs of an incident point and line.
-/

/-- The type of flags of a biplane. -/
def BiplaneFlag {P L : Type*} [Fintype P] [Fintype L] (B : Biplane P L) : Type _ := { x : P × L // B.inc x.1 x.2 }
