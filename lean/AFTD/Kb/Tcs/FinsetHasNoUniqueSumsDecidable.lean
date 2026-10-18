import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# finset_has_no_unique_sums_decidable

Topic: combinatorics   Node: a393cde7bf1d

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

Having no unique sums is a decidable property for finite subsets of an additive commutative monoid with decidable equality.
-/

/-- Having no unique sums is a decidable property for finite subsets of an additive commutative monoid with decidable equality. -/
instance finset_has_no_unique_sums_decidable {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) : Decidable (finset_has_no_unique_sums A) := by
  unfold finset_has_no_unique_sums
  infer_instance
