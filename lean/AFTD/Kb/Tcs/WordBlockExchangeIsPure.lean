import AFTD.Prelude
import AFTD.Kb.Tcs.MaskURuns
import AFTD.Kb.Tcs.WordBlockExchangeTransportForward
import AFTD.Kb.Tcs.WordBlockExchange
import AFTD.Kb.Tcs.IsPureMask

/-!
# word_block_exchange_is_pure

Topic: automata   Node: 8ff2d85b7979

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 3 and Section 4

An exchange E = (X, A, B, Y) swaps adjacent pure blocks of opposite sources from mask M if A and B are nonempty, either the slice of M for A is all true and for B is all false or vice versa, and the forward-transported mask has run count mask_u_runs (word_block_exchange_transport_forward E M) = mask_u_runs M - 1.
-/

/-- An exchange swaps adjacent pure blocks A and B from mask M, merging two U-runs. -/
def word_block_exchange_is_pure {α : Type*} (E : WordBlockExchange α) (M : List Bool) : Prop :=
  E.A ≠ [] ∧ E.B ≠ [] ∧
  ((is_pure_mask ((M.drop E.X.length).take E.A.length) true ∧
    is_pure_mask ((M.drop (E.X.length + E.A.length)).take E.B.length) false) ∨
   (is_pure_mask ((M.drop E.X.length).take E.A.length) false ∧
    is_pure_mask ((M.drop (E.X.length + E.A.length)).take E.B.length) true)) ∧
  mask_u_runs (word_block_exchange_transport_forward E M) = mask_u_runs M - 1
