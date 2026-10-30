import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdmissible

/-!
# pairwiseDisjoint_k_sum_of_isAdmissible

Topic: combinatorics   Node: c5f171601392

Provenance: helper lemma. arXiv:2610.34372, Proof of Lemma 2.1

If A is an admissible set of positive integers, then for any distinct integers k₁ and k₂, the set of sums of k₁-element subsets of A and the set of sums of k₂-element subsets of A are disjoint.
-/

/-- For an admissible set, the sets of k-element subset sums are pairwise disjoint for distinct k. -/
theorem pairwiseDisjoint_k_sum_of_isAdmissible {A : Finset ℕ} (hA : IsAdmissible A) :
    Pairwise fun k₁ k₂ =>
      Disjoint ((A.powersetCard k₁).image (Finset.sum · id))
               ((A.powersetCard k₂).image (Finset.sum · id)) := by
  intro k₁ k₂ hne
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases Finset.mem_image.mp hx1 with ⟨B, hB, rfl⟩
  rcases Finset.mem_image.mp hx2 with ⟨C, hC, hsum⟩
  rw [Finset.mem_powersetCard] at hB hC
  have hcard := hA B C hB.1 hC.1 hsum.symm
  rw [hB.2, hC.2] at hcard
  exact hne hcard
