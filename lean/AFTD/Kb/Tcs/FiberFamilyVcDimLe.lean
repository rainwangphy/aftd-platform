import AFTD.Prelude
import AFTD.Kb.Tcs.ShattersUnionOfShattersFiberFamily
import AFTD.Kb.Tcs.FinsetFiberFamily
import AFTD.Kb.Tcs.FinsetRestrictedFamily

/-!
# fiber_family_vc_dim_le

Topic: combinatorics   Node: 80792ddcaf7c

Provenance: helper lemma. arXiv:2611.06860 Lemma 2.4

Let F be a family of subsets with VC-dimension at most d on a finite ground set, and let S ⊆ J. Then the VC-dimension of the fiber family R_{J,S} is at most d - |S|.
-/

/-- The VC-dimension of the fiber family R_{J,S} is at most d - |S| when VC(F) ≤ d and S ⊆ J. -/
theorem fiber_family_vc_dim_le {α : Type*} [Fintype α] [DecidableEq α] {ℱ : Finset (Finset α)} {J S : Finset α} {d : ℕ} (hVC : ℱ.vcDim ≤ d) (hS : S ⊆ J) : (finset_fiber_family ℱ J S).vcDim ≤ d - S.card := open Finset in by
  apply Finset.sup_le
  intro T hT
  have hT_shatt : (finset_fiber_family ℱ J S).Shatters T := mem_shatterer.mp hT
  have h_disj : Disjoint S T := by
    obtain ⟨u, hu, hTu⟩ := hT_shatt (subset_refl T)
    have hu_mem : u ∈ Jᶜ.powerset := (mem_filter.mp hu).1
    rw [mem_powerset] at hu_mem
    have hTu_sub : T ⊆ u := by
      rw [← hTu]
      exact inter_subset_right
    have hTJ : Disjoint J T := disjoint_of_subset_right (hTu_sub.trans hu_mem) disjoint_compl_right
    exact hTJ.mono_left hS
  have h_shatt : ℱ.Shatters (S ∪ T) := shatters_union_of_shatters_fiber_family hS hT_shatt
  have h_card_le : (S ∪ T).card ≤ d := h_shatt.card_le_vcDim.trans hVC
  rw [card_union_of_disjoint h_disj] at h_card_le
  omega
