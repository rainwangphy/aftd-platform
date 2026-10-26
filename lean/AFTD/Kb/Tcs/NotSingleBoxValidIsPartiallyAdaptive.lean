import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.DiscreteDist

/-!
# not_single_box_valid_is_partially_adaptive

Topic: online_algorithms   Node: 45d4bf086d44

Provenance: original. Related work: refutes `single_box_valid_is_partially_adaptive`

The statement `single_box_valid_is_partially_adaptive` is false: The statement is false. `IsValidPolicy` only constrains the continuation `cont v` for values `v ∈ (inst.dist b).support`. In contrast, `IsPartiallyAdaptive` requires `aux order (cont v)` for ALL `v : ℝ`. Because the real line has infinitely many values outside the finite support of the distribution, an adversary policy can make the depth of `cont v` grow unboundedly with `v` (e.g. `chain (Nat.floor (max 0 v))`). Such a policy satisfies `IsValidPolicy` (since for `v ∈ support = {0}`, the continuation is `stop`), but cannot satisfy `IsPartiallyAdaptive` because any predetermined `order : List (Fin n)` is finite and cannot bound execution branches of arbitrary depth.
-/

theorem not_single_box_valid_is_partially_adaptive : ¬ (∀ (inst : PandoraDeadlineInstance) (h1 : inst.n = 1)
    (π : AdaptivePolicy inst.n) (hπ : IsValidPolicy inst π), IsPartiallyAdaptive π) := by
  let chain : ℕ → AdaptivePolicy 1 := fun k =>
    Nat.recOn k AdaptivePolicy.stop (fun _ ih => AdaptivePolicy.openBox 0 (fun _ => ih))
  have aux_chain_length : ∀ (k : ℕ) (order : List (Fin 1)),
      IsPartiallyAdaptive.aux order (chain k) → k ≤ order.length := by
    intro k
    induction k with
    | zero => intros; simp
    | succ k ih =>
      intro order h
      cases order with
      | nil =>
        change IsPartiallyAdaptive.aux [] (AdaptivePolicy.openBox 0 (fun _ => chain k)) at h
        rw [IsPartiallyAdaptive.aux.eq_def] at h
        contradiction
      | cons b rest =>
        change IsPartiallyAdaptive.aux (b :: rest) (AdaptivePolicy.openBox 0 (fun _ => chain k)) at h
        rw [IsPartiallyAdaptive.aux.eq_def] at h
        have := ih rest (h.2 0)
        simp only [List.length_cons]
        omega
  let myDist : DiscreteDist := {
    support := {0}
    prob := fun v => if v = 0 then 1 else 0
    prob_nonneg := by intro v hv; aesop
    sum_prob_one := by simp
    val_nonneg := by intro v hv; aesop
  }
  let myInst : PandoraDeadlineInstance := {
    n := 1
    cost := fun _ => 0
    deadline := fun _ => 1
    dist := fun _ => myDist
    cost_nonneg := by intro _; norm_num
    deadline_pos := by intro _; norm_num
  }
  let bad_policy : AdaptivePolicy 1 :=
    .openBox 0 (fun v => chain (Nat.floor (max 0 v)))
  have bad_policy_valid : IsValidPolicy myInst bad_policy := by
    dsimp [IsValidPolicy]
    rw [IsValidPolicyAux.eq_def]
    refine ⟨by simp, by decide, ?_⟩
    intro v hv
    change v ∈ myDist.support at hv
    simp only [myDist, Finset.mem_singleton] at hv
    subst hv
    have : Nat.floor (max 0 (0 : ℝ)) = 0 := by simp
    change IsValidPolicyAux myInst rfl [0] (chain (Nat.floor (max 0 0)))
    rw [this]
    change IsValidPolicyAux myInst rfl [0] AdaptivePolicy.stop
    rw [IsValidPolicyAux.eq_def]
    trivial
  have not_pa : ¬ IsPartiallyAdaptive bad_policy := by
    intro ⟨order, h⟩
    cases order with
    | nil =>
      simp only [bad_policy] at h
      rw [IsPartiallyAdaptive.aux.eq_def] at h
      contradiction
    | cons b rest =>
      simp only [bad_policy] at h
      rw [IsPartiallyAdaptive.aux.eq_def] at h
      rcases h with ⟨-, hcont⟩
      have h_v := hcont ((rest.length + 1 : ℕ) : ℝ)
      dsimp only at h_v
      have h_floor : Nat.floor (max 0 (((rest.length + 1 : ℕ) : ℝ))) = rest.length + 1 := by
        have h0 : (0 : ℝ) ≤ ((rest.length + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        rw [max_eq_right h0]
        exact Nat.floor_natCast (rest.length + 1)
      rw [h_floor] at h_v
      have h_le := aux_chain_length (rest.length + 1) rest h_v
      omega
  intro h
  have h_pa := h myInst rfl bad_policy bad_policy_valid
  exact not_pa h_pa
