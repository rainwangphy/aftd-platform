import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# finset_has_no_unique_sums

Topic: combinatorics   Node: d1bd252a82a3

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Sec. 1 (definition of NUS: |A| ≥ 2 and r_{A,2}(s) ≥ 2 for every s ∈ A + A).

A has no unique sums (is NUS): |A| ≥ 2 and every sum a + b with a, b ∈ A has at least two representations as an unordered pair from A.
-/

/-- `A` has no unique sums (is NUS): `|A| ≥ 2` and every sum `a + b` with `a, b ∈ A` has at least two representations as an unordered pair from `A`. -/
def finset_has_no_unique_sums {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A : Finset G) : Prop :=
  2 ≤ A.card ∧ ∀ a ∈ A, ∀ b ∈ A, 2 ≤ finset_unordered_sum_rep_count A (a + b)
