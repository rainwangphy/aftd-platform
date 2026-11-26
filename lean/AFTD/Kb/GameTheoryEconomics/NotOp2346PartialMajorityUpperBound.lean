import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineICDecision
import AFTD.Kb.GameTheoryEconomics.IsOnlineDistortionBounded
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost
import AFTD.Kb.GameTheoryEconomics.IsConsistentPseudometric
import AFTD.Kb.GameTheoryEconomics.IcWinnerNat
import AFTD.Kb.GameTheoryEconomics.IcWinner
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# not_op_2346_partial_majority_upper_bound

Topic: social_choice   Node: 99eb9506cdbb

Provenance: original. Related work: refutes `op_2346_partial_majority_upper_bound`

The statement `op_2346_partial_majority_upper_bound` is false: The statement is false as formalized because of a defect in the ballot definition in `ic_winner_nat`. In its body the recursive step computes, for each voter `v`,
`letI := prof v; decide (x_prev < ⟨t+1, ht⟩)`.
But `<` on `Fin T` is elaborated using Fin's global numeric `LT` instance (Fin.instLT), not the locally bound `LinearOrder` instance `prof v`. This is verifiable by `rfl`: `(letI := prof v; (a < b)) = (a.val < b.val)`. Consequently the ballot passed to the rule is the constant-`true` vector `fun _ => true` at every round (since the incumbent's index is < t+1), so `ic_winner rule prof t` depends on neither the preference profile `prof` nor the metric.

Hence no deterministic online rule can have any finite distortion bound for T ≥ 2: at T = 2, let `b := rule (Fin 1) ⟨1,_⟩ (fun _ => true)`. If `b = true` the winner at round 1 is candidate 1; take one voter at position 0, candidate 0 at 0 and candidate 1 at 1 (with the reversed linear order `1 < 0`, which is consistent); then social cost of the winner is 1 while social cost of candidate 0 is 0, contradicting `SC(winner) ≤ 3·SC(0)` (bound 2·2−1 = 3). If `b = false` the winner is candidate 0; take the mirror metric (voter at 1, candidate 0 at 0, candidate 1 at 1) with the standard order; then cost of winner is 1 while cost of candidate 1 is 0, contradicting `SC(0) ≤ 3·SC(1)`. Both are verified in Lean in the accompanying refutation.
-/

theorem not_op_2346_partial_majority_upper_bound : ¬ (∀ (T : ℕ) (_hT : 1 ≤ T),
      ∃ rule : OnlineICDecision T, is_online_distortion_bounded rule (2 * (T : ℝ) - 1)) := by
  intro h
  obtain ⟨rule, hb⟩ := h 2 (by norm_num)
  let posA : Fin 1 ⊕ Fin 2 → ℝ := fun x => Sum.elim (fun _ => (0:ℝ)) (fun c : Fin 2 => (c.val : ℝ)) x
  let posB : Fin 1 ⊕ Fin 2 → ℝ := fun x => Sum.elim (fun _ => (1:ℝ)) (fun c : Fin 2 => (c.val : ℝ)) x
  let profA : Fin 1 → LinearOrder (Fin 2) :=
    fun _ => LinearOrder.lift' (Equiv.swap (0:Fin 2) 1) (Equiv.swap (0:Fin 2) 1).injective
  let profB : Fin 1 → LinearOrder (Fin 2) := fun _ => inferInstance
  by_cases hcase : rule (Fin 1) ⟨1, by norm_num⟩ (fun _ => true) = true
  · have hw : ic_winner rule profA ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ := by
      simp only [ic_winner, ic_winner_nat, Fin.lt_def]
      norm_num
      exact hcase
    letI : PseudoMetricSpace (Fin 1 ⊕ Fin 2) := PseudoMetricSpace.induced posA (inferInstance : PseudoMetricSpace ℝ)
    have hcons : is_consistent_pseudometric (Fin 1) (Fin 2) profA := by
      intro v a b hab
      have hda : dist (Sum.inl v) (Sum.inr a) = (a.val : ℝ) := by
        change dist (posA (Sum.inl v)) (posA (Sum.inr a)) = (a.val : ℝ)
        fin_cases a <;> simp [posA, Real.dist_eq]
      have hdb : dist (Sum.inl v) (Sum.inr b) = (b.val : ℝ) := by
        change dist (posA (Sum.inl v)) (posA (Sum.inr b)) = (b.val : ℝ)
        fin_cases b <;> simp [posA, Real.dist_eq]
      rw [hda, hdb] at hab
      cases v
      fin_cases a <;> fin_cases b
      · exfalso; norm_num at hab
      · change (Equiv.swap (0:Fin 2) 1) 1 < (Equiv.swap (0:Fin 2) 1) 0
        decide
      · exfalso; norm_num at hab
      · exfalso; norm_num at hab
    have hb' := hb (Fin 1) profA hcons ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ (by norm_num)
    rw [hw] at hb'
    simp only [candidate_metric_social_cost, Fin.sum_univ_one] at hb'
    rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl] at hb'
    change dist (posA (Sum.inl 0)) (posA (Sum.inr 1)) ≤ (2 * (2:ℝ) - 1) * dist (posA (Sum.inl 0)) (posA (Sum.inr 0)) at hb'
    norm_num [posA, Real.dist_eq] at hb'
  · have hfalse : rule (Fin 1) ⟨1, by norm_num⟩ (fun _ => true) = false := by
      cases hv : rule (Fin 1) ⟨1, by norm_num⟩ (fun _ => true)
      · rfl
      · exact absurd hv hcase
    have hw : ic_winner rule profB ⟨1, by norm_num⟩ = ⟨0, by norm_num⟩ := by
      simp only [ic_winner, ic_winner_nat, Fin.lt_def]
      norm_num
      exact hfalse
    letI : PseudoMetricSpace (Fin 1 ⊕ Fin 2) := PseudoMetricSpace.induced posB (inferInstance : PseudoMetricSpace ℝ)
    have hcons : is_consistent_pseudometric (Fin 1) (Fin 2) profB := by
      intro v a b hab
      have hda : dist (Sum.inl v) (Sum.inr a) = 1 - (a.val : ℝ) := by
        change dist (posB (Sum.inl v)) (posB (Sum.inr a)) = 1 - (a.val : ℝ)
        fin_cases a <;> simp [posB, Real.dist_eq]
      have hdb : dist (Sum.inl v) (Sum.inr b) = 1 - (b.val : ℝ) := by
        change dist (posB (Sum.inl v)) (posB (Sum.inr b)) = 1 - (b.val : ℝ)
        fin_cases b <;> simp [posB, Real.dist_eq]
      rw [hda, hdb] at hab
      fin_cases a <;> fin_cases b
      · exfalso; norm_num at hab
      · exfalso; norm_num at hab
      · change (0:Fin 2) < 1
        decide
      · exfalso; norm_num at hab
    have hb' := hb (Fin 1) profB hcons ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ (le_refl _)
    rw [hw] at hb'
    simp only [candidate_metric_social_cost, Fin.sum_univ_one] at hb'
    rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl] at hb'
    change dist (posB (Sum.inl 0)) (posB (Sum.inr 0)) ≤ (2 * (2:ℝ) - 1) * dist (posB (Sum.inl 0)) (posB (Sum.inr 1)) at hb'
    norm_num [posB, Real.dist_eq] at hb'
