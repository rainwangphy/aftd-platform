import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleCardEqOfShort
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount

/-!
# restricted_cycle_count_zero_or_base_of_short

Topic: elementary_number_theory   Node: dab62809192a

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

For positive n less than 2(r+1) and an excluded set S containing lengths 1 through r, the restricted count is zero when S contains n and otherwise equals the count excluding only lengths 1 through r.
-/

theorem restricted_cycle_count_zero_or_base_of_short (r n : ℕ) (hn0 : 0 < n)
    (hn : n < 2 * (r+1)) (S : Finset ℕ) (hS : Finset.Icc 1 r ⊆ S) :
    restricted_cycle_perms_count n S =
      if n ∈ S then 0 else restricted_cycle_perms_count n (Finset.Icc 1 r) := by
  classical
  unfold restricted_cycle_perms_count
  split_ifs with hmem
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hσ
    have hb : ∀ x : Fin n,
        (Finset.univ.filter fun y => σ.SameCycle x y).card ∉ Finset.Icc 1 r := by
      intro x hx
      exact hσ x (hS hx)
    let x : Fin n := ⟨0, hn0⟩
    apply hσ x
    simpa only [restricted_cycle_card_eq_of_short r n hn σ hb x] using hmem
  · congr 1
    apply Finset.filter_congr
    intro σ hσ
    simp only [Finset.mem_coe]
    constructor
    · intro h x hx
      exact h x (hS hx)
    · intro h x
      simpa only [restricted_cycle_card_eq_of_short r n hn σ h x] using hmem
