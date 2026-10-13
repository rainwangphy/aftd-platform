import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInvert
import AFTD.Kb.Tcs.DigraphIsAcyclic

/-!
# digraph_inversion_number

Topic: graphs   Node: 48fd307e4bf5

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 1 (decycling family, inversion number).

The inversion number inv(D): the least number p of vertex sets X₁, …, X_p whose successive inversions turn D into an acyclic digraph (0 by convention when no such family exists, which never happens for a finite tournament).
-/

/-- The inversion number `inv D`: the least number of successive inversions that make
the digraph acyclic. -/
noncomputable def digraph_inversion_number {V : Type*} (D : Digraph V) : ℕ :=
  sInf {p | ∃ Xs : List (Set V), Xs.length = p ∧
    digraph_is_acyclic (Xs.foldl digraph_invert D)}
