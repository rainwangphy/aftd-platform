import AFTD.Prelude

/-!
# projective_independent_set

Topic: information   Node: c3b56f9fd81c

Provenance: formalization of a published result. Source: arXiv:2611.16447 Definition 3.4

A subset s of a projective space is projectively independent if the inclusion of its points is an independent family in the projectivization sense.
-/

/-- A subset of projective space is projectively independent if its points form an independent family. -/
def projective_independent_set {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Set (Projectivization K V)) : Prop := Projectivization.Independent ((↑) : s → Projectivization K V)
