import AFTD.Prelude
import AFTD.Kb.Tcs.TotalSimplicialDepth
import AFTD.Kb.Tcs.SimplicialDepth

/-!
# total_simplicial_depth_eq_sum_powersetCard_four

Topic: combinatorics   Node: 2d329f75f376

Provenance: helper lemma. arXiv:2610.38658 Lemma 20 -- Larger Crossing Families

The total simplicial depth of a finite point set P in the Euclidean plane is the sum over all 4-element subsets Q of P of the total simplicial depth of Q.
-/

open scoped Classical

lemma total_simplicial_depth_eq_sum_powersetCard_four_sd_eq_indicator
    (p : ℝ × ℝ) (Q : Finset (ℝ × ℝ)) (hp : p ∈ Q) (h4 : Q.card = 4) :
    simplicial_depth p Q =
      if p ∈ interior (convexHull ℝ (↑(Q.erase p) : Set (ℝ × ℝ))) then 1 else 0 := by
  have hcard : (Q.erase p).card = 3 := by
    rw [Finset.card_erase_of_mem hp, h4]
  unfold simplicial_depth
  rw [← hcard, Finset.powersetCard_self, Finset.filter_singleton]
  split_ifs with h
  · simp
  · simp

lemma total_simplicial_depth_eq_sum_powersetCard_four_sum_erase
    (p : ℝ × ℝ) (P : Finset (ℝ × ℝ)) (hp : p ∈ P) :
    ∑ Q ∈ P.powersetCard 4, (if p ∈ Q then simplicial_depth p Q else 0) =
      simplicial_depth p P := by
  rw [simplicial_depth, Finset.card_filter]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun Q _ => Q.erase p) ?_ ?_ ?_ ?_
  · intro Q hQ
    rw [Finset.mem_filter] at hQ
    obtain ⟨hQ4, hpQ⟩ := hQ
    rw [Finset.mem_powersetCard] at hQ4 ⊢
    obtain ⟨hsub, hcard⟩ := hQ4
    exact ⟨Finset.erase_subset_erase p hsub, by rw [Finset.card_erase_of_mem hpQ, hcard]⟩
  · intro Q1 hQ1 Q2 hQ2 heq
    rw [Finset.mem_filter] at hQ1 hQ2
    rw [← Finset.insert_erase hQ1.2, ← Finset.insert_erase hQ2.2, heq]
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTsub, hTcard⟩ := hT
    have hpT : p ∉ T := (Finset.subset_erase.mp hTsub).2
    refine ⟨insert p T, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.insert_subset hp (Finset.Subset.trans hTsub (Finset.erase_subset p P)),
        ?_⟩, Finset.mem_insert_self p T⟩
      rw [Finset.card_insert_of_notMem hpT, hTcard]
    · exact Finset.erase_insert hpT
  · intro Q hQ
    rw [Finset.mem_filter] at hQ
    obtain ⟨hQ4, hpQ⟩ := hQ
    rw [Finset.mem_powersetCard] at hQ4
    exact total_simplicial_depth_eq_sum_powersetCard_four_sd_eq_indicator p Q hpQ hQ4.2

lemma total_simplicial_depth_eq_sum_powersetCard_four_sum_ite_mem
    (P Q : Finset (ℝ × ℝ)) (h : Q ⊆ P) (f : ℝ × ℝ → ℕ) :
    ∑ x ∈ P, (if x ∈ Q then f x else 0) = ∑ x ∈ Q, f x := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  rw [Finset.inter_eq_right.mpr h]

lemma total_simplicial_depth_eq_sum_powersetCard_four_swap (P : Finset (ℝ × ℝ)) :
    ∑ Q ∈ P.powersetCard 4, ∑ p ∈ Q, simplicial_depth p Q =
      ∑ p ∈ P, ∑ Q ∈ P.powersetCard 4, (if p ∈ Q then simplicial_depth p Q else 0) := by
  have h1 : ∀ Q ∈ P.powersetCard 4, ∑ p ∈ Q, simplicial_depth p Q =
      ∑ p ∈ P, (if p ∈ Q then simplicial_depth p Q else 0) := by
    intro Q hQ
    rw [Finset.mem_powersetCard] at hQ
    exact (total_simplicial_depth_eq_sum_powersetCard_four_sum_ite_mem P Q hQ.1
      (fun p => simplicial_depth p Q)).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]

/-- The total simplicial depth of P decomposes as the sum of total simplicial depths over all 4-element subsets of P. -/
theorem total_simplicial_depth_eq_sum_powersetCard_four
    (P : Finset (ℝ × ℝ)) :
    total_simplicial_depth P =
      ∑ Q ∈ P.powersetCard 4, total_simplicial_depth Q := by
  unfold total_simplicial_depth
  rw [total_simplicial_depth_eq_sum_powersetCard_four_swap]
  exact Finset.sum_congr rfl
    (fun p hp => (total_simplicial_depth_eq_sum_powersetCard_four_sum_erase p P hp).symm)
