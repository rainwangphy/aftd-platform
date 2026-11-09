import AFTD.Prelude
import AFTD.Kb.Tcs.ShattersUnionOfShattersFiberFamily
import AFTD.Kb.Tcs.FiberFamilyVcDimLe
import AFTD.Kb.Tcs.FiberFamilyEqEmptyOfCardGt
import AFTD.Kb.Tcs.FinsetFiberFamily

/-!
# finset_shatters_and_vc_dim_restricted_fiber_family

Topic: combinatorics   Node: 1a1e909752e6

Provenance: formalization of a published result. Source: arXiv:2611.06860 Lemma 2.4

Let F be a family of subsets of a finite ground set with VC-dimension at most d, and let S ⊆ J. If T ⊆ Jᶜ is shattered by the fiber family R_{J,S}, then S ∪ T is shattered by F. In particular, the VC-dimension of R_{J,S} is at most d - |S| when |S| ≤ d, and R_{J,S} is empty when |S| > d.
-/

/-- Trace shattering and VC-dimension of restricted fiber families (Lemma 2.4). -/
theorem finset_shatters_and_vc_dim_restricted_fiber_family {α : Type*} [Fintype α] [DecidableEq α] (ℱ : Finset (Finset α)) {d : ℕ} (hVC : ℱ.vcDim ≤ d) (J S : Finset α) (hS : S ⊆ J) : (∀ T : Finset α, T ⊆ Jᶜ → (finset_fiber_family ℱ J S).Shatters T → ℱ.Shatters (S ∪ T)) ∧ (S.card ≤ d → (finset_fiber_family ℱ J S).vcDim ≤ d - S.card) ∧ (d < S.card → finset_fiber_family ℱ J S = ∅) :=
  ⟨fun _ _ hT => shatters_union_of_shatters_fiber_family hS hT,
   fun _ => fiber_family_vc_dim_le hVC hS,
   fiber_family_eq_empty_of_card_gt hVC hS⟩
