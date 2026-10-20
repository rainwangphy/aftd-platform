import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.IsCompatibleRepairFamily
import AFTD.Kb.Tcs.ApplyRepairs
import AFTD.Kb.Tcs.ConflictNeighborhood

/-!
# apply_repairs_is_packing

Topic: approximation   Node: 6bb818b1c7bb

Provenance: helper lemma. arXiv:2610.10036 Sec. 4.2

In a weighted k-set packing instance inst over α with decidable equality, applying a compatible family of repairs R whose sets belong to inst.family to a valid packing A yields a valid packing.
-/

/-- Applying a compatible family of repairs from the family yields a valid packing. -/
theorem apply_repairs_is_packing {α : Type*} [DecidableEq α] {k : ℕ} (inst : WeightedSetPackingInstance α k) (A : Finset (Finset α)) (R : Finset (Finset (Finset α))) (hA : is_packing inst A) (hR_sub : ∀ X ∈ R, X ⊆ inst.family) (hR_comp : is_compatible_repair_family R) : is_packing inst (apply_repairs A R) := by
  obtain ⟨hAfam, hAdisj⟩ := hA
  have hBfam : R.biUnion id ⊆ inst.family := by
    intro s hs
    rw [Finset.mem_biUnion] at hs
    obtain ⟨X, hX, hsX⟩ := hs
    exact hR_sub X hX hsX
  have hBdisj : (↑(R.biUnion id) : Set (Finset α)).PairwiseDisjoint id := hR_comp
  have hA'disj : (↑(A \ conflict_neighborhood A (R.biUnion id)) : Set (Finset α)).PairwiseDisjoint id :=
    hAdisj.subset (by intro x hx; simp only [Finset.mem_coe, Finset.mem_sdiff] at hx ⊢; exact hx.1)
  refine ⟨?_, ?_⟩
  · intro s hs
    simp only [apply_repairs, Finset.mem_union, Finset.mem_sdiff] at hs
    rcases hs with ⟨hsA, _⟩ | hsB
    · exact hAfam hsA
    · exact hBfam hsB
  · rw [apply_repairs, Finset.coe_union]
    refine hA'disj.union hBdisj ?_
    intro i hi j hj _
    simp only [Finset.mem_coe, Finset.mem_sdiff] at hi
    have hnot : ¬ ∃ x ∈ R.biUnion id, ¬ Disjoint i x := by
      intro h
      exact hi.2 (by simp only [conflict_neighborhood, Finset.mem_filter]; exact ⟨hi.1, h⟩)
    by_contra hdj
    exact hnot ⟨j, hj, hdj⟩
