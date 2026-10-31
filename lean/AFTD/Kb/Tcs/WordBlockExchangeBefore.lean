import AFTD.Prelude
import AFTD.Kb.Tcs.WordBlockExchange

/-!
# word_block_exchange_before

Topic: automata   Node: cade4bd4aa08

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 4

The word before a block exchange is the concatenation XABY.
-/

/-- The word before the exchange: XABY. -/
def word_block_exchange_before {α : Type*} (E : WordBlockExchange α) : List α :=
  E.X ++ E.A ++ E.B ++ E.Y
