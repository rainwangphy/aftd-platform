import AFTD.Prelude
import AFTD.Kb.Tcs.WordBlockExchange

/-!
# word_block_exchange_after

Topic: automata   Node: da78371be864

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 4

The word after a block exchange is the concatenation XBAY.
-/

/-- The word after the exchange: XBAY. -/
def word_block_exchange_after {α : Type*} (E : WordBlockExchange α) : List α :=
  E.X ++ E.B ++ E.A ++ E.Y
