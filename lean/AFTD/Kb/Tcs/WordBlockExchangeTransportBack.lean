import AFTD.Prelude
import AFTD.Kb.Tcs.WordBlockExchange

/-!
# word_block_exchange_transport_back

Topic: automata   Node: 5dcc12eec98a

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 4

Given a block exchange E = (X, A, B, Y) and a binary mask N of type List Bool, word_block_exchange_transport_back E N is the binary mask defined by N.take E.X.length ++ (N.drop (E.X.length + E.B.length)).take E.A.length ++ (N.drop E.X.length).take E.B.length ++ N.drop (E.X.length + E.B.length + E.A.length).
-/

/-- Transport a mask N of XBAY back to XABY. -/
def word_block_exchange_transport_back {α : Type*} (E : WordBlockExchange α) (N : List Bool) : List Bool :=
  N.take E.X.length ++
  (N.drop (E.X.length + E.B.length)).take E.A.length ++
  (N.drop E.X.length).take E.B.length ++
  N.drop (E.X.length + E.B.length + E.A.length)
