import AFTD.Prelude

/-!
# projective_independent_empty

Topic: information   Node: 6ff4e51c8d25

Provenance: helper lemma. folklore

The empty subset of any projective space is projectively independent.
-/

/-- The empty set of projective points is projectively independent. -/
theorem projective_independent_empty {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] :
    Projectivization.Independent ((↑) : (∅ : Set (Projectivization K V)) → Projectivization K V) := Projectivization.independent_iff.2 linearIndependent_empty_type
