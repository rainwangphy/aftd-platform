import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse

/-!
# digraph_reverse_reverse

Topic: graphs   Node: 7b2c2a18437d

Provenance: helper lemma. step towards tournament_dijoin_inversion_number_symm

Reversing a digraph twice yields the original digraph.
-/

/-- The reverse of the reverse of a digraph is the original digraph. -/
theorem digraph_reverse_reverse {V : Type*} (D : Digraph V) :
    digraph_reverse (digraph_reverse D) = D := by
  cases D
  rfl
