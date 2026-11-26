import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineICDecision
import AFTD.Kb.GameTheoryEconomics.IsOnlineDistortionBounded
import AFTD.Kb.GameTheoryEconomics.IcWinnerNat
import AFTD.Kb.GameTheoryEconomics.IsConsistentPseudometric
import AFTD.Kb.GameTheoryEconomics.IcWinner
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost

/-!
# not_op_2346_partial_asymptotic_upper_bound

Topic: social_choice   Node: 6a8153f1c2bb

Provenance: original. Related work: refutes `op_2346_partial_asymptotic_upper_bound`

The statement `op_2346_partial_asymptotic_upper_bound` is false: The statement `op_2346_partial_asymptotic_upper_bound` asserts the existence of C ≤ 8*sqrt(2) such that for every horizon T ≥ 1, there exists an online rule achieving metric distortion at most C*sqrt(T) + 1. Under the definition of `ic_winner_nat`, the comparison passed to the decision rule at round t+1 is `pref v = decide (x_prev < ⟨t+1, ht⟩)`, which evaluates the numeric order `instLTFin` on `Fin T` instead of the voter's preference `prof v`. As a consequence, the elected candidate is independent of the voter preference profile. For horizon T = 2 and any candidate decision rule, an adversarial metric on 1 voter can place candidate y at distance 0 and the rule's winner x at distance 1, giving cost 0 for y and cost 1 for x, which requires 1 ≤ D * 0 = 0, a contradiction. Thus no rule can achieve any finite distortion bound for T = 2.
-/

theorem not_op_2346_partial_asymptotic_upper_bound : ¬ (∃ C : ℝ, C ≤ 8 * Real.sqrt 2 ∧
      ∀ (T : ℕ) (_hT : 1 ≤ T),
        ∃ rule : OnlineICDecision T,
          is_online_distortion_bounded rule (C * Real.sqrt (T : ℝ) + 1)) := by
  have irrel : ∀ {T : ℕ} (rule : OnlineICDecision T) {V : Type} [Fintype V]
      (prof prof' : V → LinearOrder (Fin T)) (t : Fin T),
      ic_winner rule prof t = ic_winner rule prof' t := by
    intro T rule V inst prof prof' t
    have h : ∀ (t : ℕ) (ht : t < T), ic_winner_nat rule prof t ht = ic_winner_nat rule prof' t ht := by
      intro t
      induction t with
      | zero => intro ht; rw [ic_winner_nat.eq_def, ic_winner_nat.eq_def]
      | succ t ih =>
        intro ht
        rw [ic_winner_nat.eq_def, ic_winner_nat.eq_def]
        simp only
        rw [ih]
    exact h t.val t.isLt
  have distortion_bound_unattainable : ∀ (T : ℕ) (hT : 2 ≤ T)
      (rule : OnlineICDecision T) (D : ℝ), ¬ is_online_distortion_bounded rule D := by
    intro T hT rule D h_bd
    let prof₀ : Fin 1 → LinearOrder (Fin T) :=
      fun _ => LinearOrder.lift' (fun c : Fin T => (c : ℕ)) (fun a b h => Fin.ext h)
    have ht_lt : T - 1 < T := by omega
    let t : Fin T := ⟨T - 1, ht_lt⟩
    let x : Fin T := ic_winner rule prof₀ t
    have hy_lt : (if x.val = 0 then 1 else 0) < T := by split_ifs <;> omega
    let y : Fin T := ⟨if x.val = 0 then 1 else 0, hy_lt⟩
    have hxy : x ≠ y := by
      intro heq
      have hval : x.val = y.val := congr_arg Fin.val heq
      dsimp [y] at hval
      split_ifs at hval <;> omega
    have hyt : y ≤ t := by
      show y.val ≤ t.val
      dsimp [y, t]
      split_ifs <;> omega
    let key : Fin T → ℕ := fun c => if c = y then T + 1 else c.val
    have hkey_inj : Function.Injective key := by
      intro a b hab
      dsimp [key] at hab
      split_ifs at hab with ha hb hb
      · exact ha.trans hb.symm
      · exfalso
        have : a = y := ha
        have : b.val < T := b.isLt
        omega
      · exfalso
        have : b = y := hb
        have : a.val < T := a.isLt
        omega
      · exact Fin.ext hab
    let prof : Fin 1 → LinearOrder (Fin T) := fun _ => LinearOrder.lift' key hkey_inj
    let f : Fin 1 ⊕ Fin T → ℝ := fun z => match z with
      | Sum.inl _ => 0
      | Sum.inr c => if c = y then 0 else 1
    let instPM : PseudoMetricSpace (Fin 1 ⊕ Fin T) := PseudoMetricSpace.induced f inferInstance
    have hcons : @is_consistent_pseudometric (Fin 1) (Fin T) instPM prof := by
      intro v a b hdist
      have hdist' : dist (f (Sum.inl v)) (f (Sum.inr a)) < dist (f (Sum.inl v)) (f (Sum.inr b)) := hdist
      rw [Real.dist_eq, Real.dist_eq] at hdist'
      dsimp [f] at hdist'
      have h_cases : a = y ∧ b ≠ y := by
        split_ifs at hdist' with ha hb hb
        · exfalso; norm_num at hdist'
        · exact ⟨ha, hb⟩
        · exfalso; norm_num at hdist'
        · exfalso; norm_num at hdist'
      show @LT.lt (Fin T) (@Preorder.toLT (Fin T) (@PartialOrder.toPreorder (Fin T)
        (@LinearOrder.toPartialOrder (Fin T) (prof v)))) b a
      change key b < key a
      dsimp [key]
      have ha : a = y := h_cases.1
      have hb : b ≠ y := h_cases.2
      simp [ha, hb]
    have h_bound_inst := @h_bd (Fin 1) _ _ instPM prof hcons t y hyt
    have h_winner : ic_winner rule prof t = x := irrel rule prof prof₀ t
    rw [h_winner] at h_bound_inst
    have hcy : @candidate_metric_social_cost (Fin 1) _ (Fin T) instPM y = 0 := by
      dsimp [candidate_metric_social_cost]
      rw [Fin.sum_univ_one]
      show dist (f (Sum.inl 0)) (f (Sum.inr y)) = 0
      rw [Real.dist_eq]
      dsimp [f]
      simp
    have hcx : @candidate_metric_social_cost (Fin 1) _ (Fin T) instPM x = 1 := by
      dsimp [candidate_metric_social_cost]
      rw [Fin.sum_univ_one]
      show dist (f (Sum.inl 0)) (f (Sum.inr x)) = 1
      rw [Real.dist_eq]
      dsimp [f]
      split_ifs with h
      · exact False.elim (hxy h)
      · norm_num
    rw [hcy, hcx] at h_bound_inst
    linarith
  intro ⟨C, _, hT⟩
  obtain ⟨rule, h_rule⟩ := hT 2 (by norm_num)
  exact distortion_bound_unattainable 2 (by norm_num) rule (C * Real.sqrt 2 + 1) h_rule
