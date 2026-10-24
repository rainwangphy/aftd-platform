import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedPairSumCount

/-!
# highRepSet

Topic: combinatorics   Node: 12b10bbec079

Provenance: helper lemma. step towards restricted_diff_card_le_of_missing

The set P(A) of all group elements having more than two ordered restricted pair representations from A.
-/

/-- Elements with more than two ordered restricted pair representations (the paper's set P). -/
def highRepSet {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (A : Finset G) : Finset G := Finset.univ.filter (fun x => 2 < orderedPairSumCount A x)
