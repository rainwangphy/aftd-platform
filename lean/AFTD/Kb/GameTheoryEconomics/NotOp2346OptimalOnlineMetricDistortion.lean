import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineICDecision
import AFTD.Kb.GameTheoryEconomics.IsOnlineDistortionBounded
import AFTD.Kb.GameTheoryEconomics.IsOptimalOnlineDistortion
import AFTD.Kb.GameTheoryEconomics.IcWinnerNat
import AFTD.Kb.GameTheoryEconomics.IsConsistentPseudometric
import AFTD.Kb.GameTheoryEconomics.IcWinner
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost

/-!
# not_op_2346_optimal_online_metric_distortion

Topic: social_choice   Node: 510d549550ea

Provenance: original. Related work: refutes `op_2346_optimal_online_metric_distortion`

The statement `op_2346_optimal_online_metric_distortion` is false: The statement asserts the existence of Δ_3 in [3, 5] such that `is_optimal_online_distortion 3 Δ_3`. However, under the formal definition of `ic_winner_nat`, the challenger-preference vector passed to the decision rule at round t+1 is `pref v = decide (x_prev < ⟨t+1, ht⟩)`, which evaluates the numeric order `instLTFin` on `Fin T` rather than the voter's preference `prof v`. As a consequence, the elected candidate is independent of the voter profiles. For horizon T = 3 (and indeed any T ≥ 2) and any candidate decision rule, an adversarial profile on a single voter can set the rival candidate y at distance 0 and all other candidates (including the rule's predetermined winner x) at distance 1 while maintaining metric consistency. This makes the social cost of y equal to 0 while the winner's social cost is 1, so no finite distortion bound D can be satisfied (requiring 1 ≤ D * 0). Therefore, `is_online_distortion_bounded rule D` is false for every rule and every D, meaning `is_optimal_online_distortion 3 Δ_3` cannot hold for any Δ_3.
-/

theorem not_op_2346_optimal_online_metric_distortion : ¬ (∃ (C_star : ℝ) (Δ_3 : ℝ),
      2 ≤ C_star ∧ C_star ≤ 8 * Real.sqrt 2 ∧
      3 ≤ Δ_3 ∧ Δ_3 ≤ 5 ∧
      is_optimal_online_distortion 3 Δ_3 ∧
      ∀ ε > 0, ∃ T_0 : ℕ, ∀ T ≥ T_0, ∀ D : ℝ,
        is_optimal_online_distortion T D →
          (C_star - ε) * Real.sqrt (T : ℝ) ≤ D ∧ D ≤ (C_star + ε) * Real.sqrt (T : ℝ)) := by
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
  intro ⟨C_star, Δ_3, _, _, _, _, h_opt, _⟩
  rcases h_opt with ⟨h_achieve, _⟩
  obtain ⟨rule, h_rule⟩ := h_achieve 1 zero_lt_one
  exact distortion_bound_unattainable 3 (by norm_num) rule (Δ_3 + 1) h_rule
