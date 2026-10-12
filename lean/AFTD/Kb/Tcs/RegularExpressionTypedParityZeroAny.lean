import AFTD.Prelude
import AFTD.Kb.Tcs.RegularExpressionTypedParity

/-!
# regular_expression_typed_parity_zero_any

Topic: automata   Node: 2f40e9dee43d

Provenance: helper lemma. Sanity lemma for regular_expression_typed_parity (arXiv:2610.11717 (Every Regular Language Has a Bipartite Cactus Automaton), Sec. 3.1).

The empty expression ∅ is typed with either parity.
-/

theorem regular_expression_typed_parity_zero_any {α : Type*} (p : ZMod 2) :
    regular_expression_typed_parity (0 : RegularExpression α) p := trivial
