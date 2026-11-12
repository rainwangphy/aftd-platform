import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasRandomizedOnlineMmsBarrierBreaker
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.RandomizedOnlineChoreAlgorithm
import AFTD.Kb.GameTheoryEconomics.DeterministicOnlineChoreRule
import AFTD.Kb.GameTheoryEconomics.ExpectedChoreCost
import AFTD.Kb.GameTheoryEconomics.ChorePropShareLeMaximinShare
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# op913_randomized_mms_barrier_under_upgrade_recourse

Topic: fair_division   Node: 7f6db8ac969d

Provenance: formalization of a published result. Source: arXiv:2611.00432 after Thm 4.1

Open problem OP-913 (arXiv:2611.00432, after Thm 4.1): for every number of agents n ≥ 2, has_randomized_online_mms_barrier_breaker n holds, asserting the existence of a randomized prediction-free online algorithm with upgrade recourse and an ε > 0 beating the 2 - 1/n barrier in expected MMS cost against an oblivious adversary.
-/

noncomputable def op913_constant_rule {n : ℕ} (a : Fin n) : DeterministicOnlineChoreRule n where
  alloc := fun _ _ _ => a
  prediction_free := by intros; rfl
  upgrade_recourse := by
    intro c hc m i
    refine ⟨fun d => ⟨d.val.castSucc, d.property⟩, ?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      have heq : x.val.castSucc = y.val.castSucc := congrArg Subtype.val h
      exact Fin.ext (congrArg (fun d : Fin (m + 1) => d.val) heq)
    · intro d
      exact le_rfl

noncomputable def op913_lottery (n : ℕ) [NeZero n] : RandomizedOnlineChoreAlgorithm n where
  Ω := Fin n
  dist := PMF.uniformOfFintype (Fin n)
  rule := op913_constant_rule

/-- Open Problem OP-913: randomized MMS approximation barrier under upgrade recourse. -/
theorem op913_randomized_mms_barrier_under_upgrade_recourse (n : ℕ) (hn : 2 ≤ n) :
    has_randomized_online_mms_barrier_breaker n := by
  letI : NeZero n := ⟨by omega⟩
  refine ⟨1 - 1 / (n : ℝ), ?_, op913_lottery n, ?_⟩
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by positivity
    have : 1 / (n : ℝ) < 1 := (div_lt_one hn0).2 (by linarith)
    linarith
  · intro m c hc i
    have hsum : expected_chore_cost (op913_lottery n) c m i =
        (∑ j : Fin m, c i j.val) / (n : ℝ) := by
      classical
      change (∑' ω : Fin n, (PMF.uniformOfFintype (Fin n) ω).toReal *
        additive_valuation (fun j : Fin m => c i j.val)
          (bundle_of (fun _ => ω) i)) = _
      rw [tsum_fintype]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      have hb (ω : Fin n) : additive_valuation (fun j : Fin m => c i j.val)
          (bundle_of (fun _ => ω) i) = if ω = i then ∑ j : Fin m, c i j.val else 0 := by
        by_cases h : ω = i <;> simp [bundle_of, additive_valuation, h]
      simp only [hb, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

    rw [hsum]
    have h := chore_prop_share_le_maximin_share n m (fun j => c i j.val)
    convert h using 1 <;> ring
