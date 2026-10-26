import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.PandoraIsReservation

/-!
# pandora_exists_reservation

Topic: online_algorithms   Node: e49f37eef4e1

Provenance: helper lemma. Helper for op184_partially_adaptive_half_approximation: arXiv:2610.13775 Section 3, Lemma 1 / Section 3.1 (existence of reservation values)

Every Pandora instance with deadlines has reservation values: for every box i there is r_i with E[(v_i - r_i)^+] = c_i.
-/

theorem pandora_exists_reservation (inst : PandoraDeadlineInstance) :
    ∃ r : Fin inst.n → ℝ, pandora_is_reservation inst r := by
  have h : ∀ i : Fin inst.n, ∃ r_i : ℝ, ∑ v ∈ (inst.dist i).support, (inst.dist i).prob v * max (v - r_i) 0 = inst.cost i := by
    intro i
    let dist := inst.dist i
    let c := inst.cost i
    have hc : 0 ≤ c := inst.cost_nonneg i
    let f := fun r : ℝ => ∑ v ∈ dist.support, dist.prob v * max (v - r) 0
    let a := -c
    let b := max 0 (∑ v ∈ dist.support, v)
    have hab : a ≤ b := by
      dsimp [a, b]
      have : -c ≤ 0 := neg_nonpos.mpr hc
      exact le_trans this (le_max_left 0 _)
    have hcont : ContinuousOn f (Set.Icc a b) := by
      apply Continuous.continuousOn
      continuity
    have hfa : c ≤ f a := by
      dsimp [f, a]
      have h1 : ∀ v ∈ dist.support, c ≤ max (v - (-c)) 0 := by
        intro v hv
        have hv_nonneg : 0 ≤ v := dist.val_nonneg v hv
        have : c ≤ v - (-c) := by linarith
        exact le_trans this (le_max_left (v - (-c)) 0)
      have h2 : ∀ v ∈ dist.support, dist.prob v * c ≤ dist.prob v * max (v - (-c)) 0 := by
        intro v hv
        exact mul_le_mul_of_nonneg_left (h1 v hv) (dist.prob_nonneg v hv)
      have h3 : ∑ v ∈ dist.support, dist.prob v * c ≤ ∑ v ∈ dist.support, dist.prob v * max (v - (-c)) 0 :=
        Finset.sum_le_sum h2
      have h4 : ∑ v ∈ dist.support, dist.prob v * c = c := by
        rw [← Finset.sum_mul, dist.sum_prob_one, one_mul]
      rwa [h4] at h3
    have hfb : f b ≤ c := by
      dsimp [f, b]
      have hb : ∀ v ∈ dist.support, max (v - max 0 (∑ v ∈ dist.support, v)) 0 = 0 := by
        intro v hv
        have hle1 : v ≤ ∑ w ∈ dist.support, w := Finset.single_le_sum (fun w hw => dist.val_nonneg w hw) hv
        have hle2 : ∑ w ∈ dist.support, w ≤ max 0 (∑ v ∈ dist.support, v) := le_max_right 0 _
        have hle : v ≤ b := le_trans hle1 hle2
        have : v - b ≤ 0 := sub_nonpos.mpr hle
        exact max_eq_right this
      have hsum : ∑ v ∈ dist.support, dist.prob v * max (v - max 0 (∑ v ∈ dist.support, v)) 0 = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [hb v hv, mul_zero]
      rw [hsum]
      exact hc
    have hc_mem : c ∈ Set.Icc (f b) (f a) := ⟨hfb, hfa⟩
    have hivt := intermediate_value_Icc' hab hcont hc_mem
    rcases hivt with ⟨r, _, hr⟩
    exact ⟨r, hr⟩
  dsimp [pandora_is_reservation]
  exact Classical.skolem.mp h
