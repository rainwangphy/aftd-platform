import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationBundleSumIte

/-!
# chore_prop_share_le_maximin_share

Topic: fair_division   Node: 8305b1ec7745

Provenance: helper lemma. step towards ex_post_mms_chore_lottery_below_four_thirds

For any number of agents n >= 1, items m, and additive chore cost function u, the proportional share (sum of costs divided by n) is at most the chore maximin share.
-/

/-- For any number of agents n >= 1, items m, and additive chore cost function u, the proportional share (sum of costs divided by n) is at most the chore maximin share. -/
theorem chore_prop_share_le_maximin_share (n m : ℕ) [NeZero n] (u : Fin m → ℝ) :
  (∑ e : Fin m, u e) / (n : ℝ) ≤ chore_maximin_share n u := by
  change (∑ e : Fin m, u e) / (n : ℝ) ≤ ⨅ P : Fin m → Fin n, ⨆ k : Fin n, additive_valuation u (bundle_of P k)
  apply le_ciInf
  intro P
  have hsum : ∑ k : Fin n, additive_valuation u (bundle_of P k) = ∑ e : Fin m, u e := by
    simp_rw [additive_valuation_bundle_sum_ite]
    rw [Finset.sum_comm]
    simp
  have h_ex : ∃ k : Fin n, (∑ e : Fin m, u e) / (n : ℝ) ≤ additive_valuation u (bundle_of P k) := by
    by_contra! h
    have hlt : ∑ k : Fin n, additive_valuation u (bundle_of P k) <
        ∑ k : Fin n, (∑ e : Fin m, u e) / (n : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro i _
      exact h i
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    rw [mul_div_cancel₀ _ hn] at hlt
    exact lt_irrefl _ hlt
  rcases h_ex with ⟨k, hk⟩
  have hbdd : BddAbove (Set.range (fun k : Fin n => additive_valuation u (bundle_of P k))) :=
    (Set.finite_range _).bddAbove
  exact le_trans hk (le_ciSup hbdd k)
