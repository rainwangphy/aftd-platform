import AFTD.Prelude
import AFTD.Kb.Tcs.WordBlockExchange

/-!
# word_block_exchange_transport_forward

Topic: automata   Node: e9be53ba781d

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 4

Given a block exchange E = (X, A, B, Y) and a binary mask M of type List Bool, word_block_exchange_transport_forward E M is the binary mask defined by M.take E.X.length ++ (M.drop (E.X.length + E.A.length)).take E.B.length ++ (M.drop E.X.length).take E.A.length ++ M.drop (E.X.length + E.A.length + E.B.length).
-/

/-- Transport a mask M of XABY forward to XBAY. -/
def word_block_exchange_transport_forward {α : Type*} (E : WordBlockExchange α) (M : List Bool) : List Bool :=
  M.take E.X.length ++
  (M.drop (E.X.length + E.A.length)).take E.B.length ++
  (M.drop E.X.length).take E.A.length ++
  M.drop (E.X.length + E.A.length + E.B.length)
