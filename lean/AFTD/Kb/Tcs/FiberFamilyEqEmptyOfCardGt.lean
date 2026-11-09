import AFTD.Prelude
import AFTD.Kb.Tcs.ShattersUnionOfShattersFiberFamily
import AFTD.Kb.Tcs.FinsetFiberFamily

/-!
# fiber_family_eq_empty_of_card_gt

Topic: combinatorics   Node: 5082f9d8c27d

Provenance: helper lemma. arXiv:2611.06860 Lemma 2.4

Let F be a family of subsets with VC-dimension at most d on a finite ground set, and let S ⊆ J with |S| > d. Then the fiber family R_{J,S} is empty.
-/

/-- If |S| > d and VC(F) ≤ d, then the fiber family R_{J,S} is empty. -/
theorem fiber_family_eq_empty_of_card_gt {α : Type*} [Fintype α] [DecidableEq α] {ℱ : Finset (Finset α)} {J S : Finset α} {d : ℕ} (hVC : ℱ.vcDim ≤ d) (hS : S ⊆ J) (hSd : d < S.card) : finset_fiber_family ℱ J S = ∅ := by
  by_contra h_ne
  have h_nonempty : (finset_fiber_family ℱ J S).Nonempty := Finset.nonempty_iff_ne_empty.2 h_ne
  have h_shat_empty : (finset_fiber_family ℱ J S).Shatters ∅ := Finset.shatters_empty.2 h_nonempty
  have h_shat_union := shatters_union_of_shatters_fiber_family hS h_shat_empty
  rw [Finset.union_empty] at h_shat_union
  have h_card_le := h_shat_union.card_le_vcDim
  omega
