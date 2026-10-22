import AFTD.Prelude
import AFTD.Kb.Tcs.IsPosetRealizer

/-!
# poset_dimension

Topic: combinatorics   Node: f811cb7798ae

Provenance: formalization of a published result. Source: Dushnik and Miller, Partially ordered sets, Amer. J. Math. 63 (1941), pp. 600-620

For a relation r : α → α → Prop on α, poset_dimension r is the infimum in ℕ of the set of natural numbers d such that there exists a family of linear orders R : Fin d → LinearOrder α satisfying is_poset_realizer r R.
-/

/-- The Dushnik-Miller dimension of a relation r on α as the minimum size of a realizer. -/
noncomputable def poset_dimension {α : Type*} (r : α → α → Prop) : ℕ :=
  sInf {d : ℕ | ∃ R : Fin d → LinearOrder α, is_poset_realizer r R}
