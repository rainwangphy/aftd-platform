import AFTD.Prelude

/-!
# orderedPairSumCount

Topic: combinatorics   Node: 598208b72975

Provenance: helper lemma. step towards restricted_diff_card_le_of_missing

The restricted two-fold representation function ν_A(x): the number of ordered pairs (a, b) of distinct elements of A with a + b = x.
-/

/-- Number of ordered representations of x as a sum of two distinct elements of A. -/
def orderedPairSumCount {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (x : G) : ℕ := ((A ×ˢ A).filter (fun p : G × G => p.1 ≠ p.2 ∧ p.1 + p.2 = x)).card
