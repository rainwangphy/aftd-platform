import AFTD.Prelude
import AFTD.Kb.Tcs.RegularExpressionTypedParity

/-!
# not_regular_expression_typed_parity_char_zero

Topic: automata   Node: 03d84ff6469a

Provenance: helper lemma. Sanity lemma for regular_expression_typed_parity (arXiv:2610.11717 (Every Regular Language Has a Bipartite Cactus Automaton), Sec. 3.1).

A single letter is not typed with parity 0.
-/

theorem not_regular_expression_typed_parity_char_zero {α : Type*} (a : α) :
    ¬ regular_expression_typed_parity (RegularExpression.char a) 0 := by
  simp [regular_expression_typed_parity]
