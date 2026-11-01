import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleLengthSupport
import AFTD.Kb.NumberTheory.RestrictedCycleExactSupportCount
import AFTD.Kb.NumberTheory.RestrictedCycleSameCycleCardBounds
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount

/-!
# restricted_cycle_count_as_support_sum

Topic: elementary_number_theory   Node: 3b8eebd984ca

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

If A is contained in the interval of lengths from r+1 through n, the number of permutations avoiding lengths 1 through r and avoiding the lengths in that interval outside A equals the sum of exact-support counts over all subsets of A.
-/

theorem restricted_cycle_count_as_support_sum (r n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc (r+1) n) :
    restricted_cycle_perms_count n (Finset.Icc 1 r ∪ (Finset.Icc (r+1) n \ A)) =
      ∑ P ∈ A.powerset, restricted_cycle_exact_support_count n P := by
  classical
  simp only [restricted_cycle_exact_support_count]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  unfold restricted_cycle_perms_count
  congr 1
  apply Finset.filter_congr
  intro σ hσ
  simp only [Finset.mem_coe, Finset.mem_powerset, restricted_cycle_length_support, Finset.image_subset_iff,
    Finset.mem_univ, forall_const]
  constructor
  · intro h x
    have hx := restricted_cycle_same_cycle_card_bounds n σ x
    specialize h x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc] at h hx
    by_contra hnot
    apply h
    right
    exact ⟨⟨by omega, hx.2⟩, hnot⟩
  · intro h x hx
    have hAx := hA (h x)
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc] at hx hAx
    rcases hx with hx | hx
    · omega
    · exact hx.2 (h x)
