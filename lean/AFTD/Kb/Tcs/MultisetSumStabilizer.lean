import AFTD.Prelude
import AFTD.Kb.Tcs.MultisetSumFinset

/-!
# multiset_sum_stabilizer

Topic: combinatorics   Node: 1f5b43979c12

Provenance: helper lemma. step towards regular_sequence_additive_basis_cp_cnp

The stabilizer of the set of all submultiset sums of S: the additive subgroup of elements h that fix Σ₀(S) setwise under translation u ↦ u + h.
-/

/-- The stabilizer (period subgroup) of multiset_sum_finset S under translation, as an additive subgroup. -/
noncomputable def multiset_sum_stabilizer {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Multiset G) : AddSubgroup G where
  carrier := {h | ∀ u, (u ∈ multiset_sum_finset S ↔ u + h ∈ multiset_sum_finset S)}
  zero_mem' := by intro u; rw [add_zero]
  add_mem' := by intro a b ha hb u; rw [ha u, hb (u + a)]; abel
  neg_mem' := by
    intro a ha u
    have h := ha (u + (-a)); rw [show u + (-a) + a = u by abel] at h; exact h.symm
