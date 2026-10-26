import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.PandoraThresholdPolicy
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.PandoraThresholdPolicyNil
import AFTD.Kb.Tcs.PandoraThresholdPolicyCons

/-!
# pandora_threshold_policy_valid

Topic: online_algorithms   Node: fabb40e623c2

Provenance: helper lemma. Helper for op184_partially_adaptive_half_approximation: arXiv:2610.13775 Section 3, Theorem 1 proof (the algorithm respects deadlines and is partially adaptive)

A threshold policy on a duplicate-free list whose j-th box has deadline at least j is a valid policy and is partially adaptive.
-/

lemma pandora_threshold_policy_valid_partially_adaptive {n : ℕ} (order : List (Fin n)) (t : ℝ) :
    IsPartiallyAdaptive (pandora_threshold_policy order t) := by
  use order
  induction' order with b rest ih
  · trivial
  · rw [pandora_threshold_policy_cons]
    dsimp [IsPartiallyAdaptive.aux]
    refine ⟨rfl, fun v => ?_⟩
    split_ifs
    · cases rest <;> trivial
    · exact ih

lemma pandora_threshold_policy_valid_aux (inst : PandoraDeadlineInstance) (t : ℝ)
    (opened : List (Fin inst.n)) (rem : List (Fin inst.n))
    (hnd : rem.Nodup)
    (hdisj : ∀ x ∈ rem, x ∉ opened)
    (hdl : ∀ (j : ℕ) (hj : j < rem.length), opened.length + j + 1 ≤ inst.deadline (rem.get ⟨j, hj⟩)) :
    IsValidPolicyAux inst rfl opened (pandora_threshold_policy rem t) := by
  induction' rem with b rest ih generalizing opened
  · rw [pandora_threshold_policy_nil]
    trivial
  · rw [pandora_threshold_policy_cons]
    dsimp [IsValidPolicyAux]
    have hb_not_in : b ∉ opened := hdisj b List.mem_cons_self
    have hdl_b : opened.length + 1 ≤ inst.deadline b := hdl 0 (Nat.succ_pos rest.length)
    refine ⟨hb_not_in, hdl_b, fun v hv => ?_⟩
    split_ifs
    · trivial
    · apply ih (b :: opened)
      · exact (List.nodup_cons.mp hnd).2
      · intro x hx h_in
        rcases List.mem_cons.mp h_in with heq | h_in_opened
        · subst heq
          exact (List.nodup_cons.mp hnd).1 hx
        · exact hdisj x (List.mem_cons_of_mem b hx) h_in_opened
      · intro j hj
        have h := hdl (j + 1) (Nat.succ_lt_succ hj)
        change (opened.length + 1) + j + 1 ≤ inst.deadline (rest.get ⟨j, hj⟩)
        have heq : (b :: rest).get ⟨j + 1, Nat.succ_lt_succ hj⟩ = rest.get ⟨j, hj⟩ := rfl
        rw [← heq]
        omega

theorem pandora_threshold_policy_valid (inst : PandoraDeadlineInstance) (t : ℝ)
    (order : List (Fin inst.n)) (hnd : order.Nodup)
    (hdl : ∀ (j : ℕ) (hj : j < order.length), j + 1 ≤ inst.deadline (order.get ⟨j, hj⟩)) :
    IsValidPolicy inst (pandora_threshold_policy order t) ∧
      IsPartiallyAdaptive (pandora_threshold_policy order t) := by
  refine ⟨?_, pandora_threshold_policy_valid_partially_adaptive order t⟩
  apply pandora_threshold_policy_valid_aux inst t [] order hnd
  · intro x _ h_in
    exact List.not_mem_nil h_in
  · intro j hj
    simpa using hdl j hj
