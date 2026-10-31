import AFTD.Prelude
import AFTD.Kb.Tcs.WordBlockExchange
import AFTD.Kb.Tcs.WordProj

/-!
# word_block_exchange_is_commuting

Topic: automata   Node: eb8f2661b625

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 4, equation (1)

A mask N of XBAY is commuting for exchange E if its U-projections and V-projections on the exchanged blocks satisfy A_U B_U = B_U A_U and A_V B_V = B_V A_V.
-/

/-- A mask N of XBAY is commuting for E if A_U B_U = B_U A_U and A_V B_V = B_V A_V. -/
def word_block_exchange_is_commuting {α : Type*} (E : WordBlockExchange α) (N : List Bool) : Prop :=
  let maskB := (N.drop E.X.length).take E.B.length
  let maskA := (N.drop (E.X.length + E.B.length)).take E.A.length
  let AU := word_proj true E.A maskA
  let BU := word_proj true E.B maskB
  let AV := word_proj false E.A maskA
  let BV := word_proj false E.B maskB
  AU ++ BU = BU ++ AU ∧ AV ++ BV = BV ++ AV
