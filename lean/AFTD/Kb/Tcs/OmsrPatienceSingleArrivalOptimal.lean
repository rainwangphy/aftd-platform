import AFTD.Prelude
import AFTD.Kb.Tcs.OfflineOptValue
import AFTD.Kb.Tcs.RandomizedOMSRPolicy
import AFTD.Kb.Tcs.ExpectedOnlineValue
import AFTD.Kb.Tcs.OptDP
import AFTD.Kb.Tcs.OfflineArrival
import AFTD.Kb.Tcs.OnlinePolicyValue
import AFTD.Kb.Tcs.OMSRArrival
import AFTD.Kb.Tcs.ProbeValue
import AFTD.Kb.Tcs.IsValidProbeSeq

/-!
# omsr_patience_single_arrival_optimal

Topic: online_algorithms   Node: 3c29ee566b5e

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:415

For all n and all non-negative weights w, there exists a randomized online policy R for n resources such that on every arrival list arrs with at most one arrival (arrs.length ≤ 1), offlineOptValue w arrs ≤ expectedOnlineValue w R arrs.
-/

open Classical

private noncomputable def omsr_patience_single_arrival_optimal_bestVal {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) : Finset (Fin n) → ℕ → ℝ
  | _, 0 => 0
  | A, k + 1 =>
      if h : A.Nonempty then
        max 0 (A.sup' h (fun i => arr.prob i * w i + (1 - arr.prob i) *
          omsr_patience_single_arrival_optimal_bestVal arr w (A.erase i) k))
      else 0

private theorem omsr_patience_single_arrival_optimal_bestVal_nonneg {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) (A : Finset (Fin n)) (k : ℕ) :
    0 ≤ omsr_patience_single_arrival_optimal_bestVal arr w A k := by
  induction k generalizing A with
  | zero => simp [omsr_patience_single_arrival_optimal_bestVal]
  | succ k ih =>
    by_cases h : A.Nonempty
    · rw [omsr_patience_single_arrival_optimal_bestVal, dif_pos h]
      exact le_max_left _ _
    · rw [omsr_patience_single_arrival_optimal_bestVal, dif_neg h]

private theorem omsr_patience_single_arrival_optimal_bestVal_step_le {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) {A : Finset (Fin n)} (h : A.Nonempty) {i : Fin n} (hi : i ∈ A) (k : ℕ) :
    arr.prob i * w i + (1 - arr.prob i) *
      omsr_patience_single_arrival_optimal_bestVal arr w (A.erase i) k
      ≤ omsr_patience_single_arrival_optimal_bestVal arr w A (k + 1) := by
  rw [omsr_patience_single_arrival_optimal_bestVal, dif_pos h]
  exact le_trans (Finset.le_sup' (fun i => arr.prob i * w i + (1 - arr.prob i) *
      omsr_patience_single_arrival_optimal_bestVal arr w (A.erase i) k) hi) (le_max_right _ _)

private theorem omsr_patience_single_arrival_optimal_probeValue_zero_indep {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) (S S' : Finset (Fin n)) (L : List (Fin n)) :
    probeValue arr w (fun _ => (0:ℝ)) S L = probeValue arr w (fun _ => (0:ℝ)) S' L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [probeValue]
    rw [ih]

private theorem omsr_patience_single_arrival_optimal_bestVal_attained {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) (A : Finset (Fin n)) (k : ℕ) :
    ∃ L : List (Fin n), L.Nodup ∧ (∀ i ∈ L, i ∈ A) ∧ L.length ≤ k ∧
      probeValue arr w (fun _ => 0) A L = omsr_patience_single_arrival_optimal_bestVal arr w A k := by
  induction k generalizing A with
  | zero => exact ⟨[], List.nodup_nil, by simp, by simp, rfl⟩
  | succ k ih =>
    by_cases hA : A.Nonempty
    · have hbest : omsr_patience_single_arrival_optimal_bestVal arr w A (k + 1)
          = max 0 (A.sup' hA (fun i => arr.prob i * w i + (1 - arr.prob i) *
              omsr_patience_single_arrival_optimal_bestVal arr w (A.erase i) k)) := by
        simp only [omsr_patience_single_arrival_optimal_bestVal, dif_pos hA]
      by_cases hX : A.sup' hA (fun i => arr.prob i * w i + (1 - arr.prob i) *
          omsr_patience_single_arrival_optimal_bestVal arr w (A.erase i) k) ≤ 0
      · refine ⟨[], List.nodup_nil, by simp, by simp, ?_⟩
        rw [hbest, max_eq_left hX]
        rfl
      · have hXpos : 0 < A.sup' hA (fun i => arr.prob i * w i + (1 - arr.prob i) *
            omsr_patience_single_arrival_optimal_bestVal arr w (A.erase i) k) := not_le.mp hX
        obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' hA (fun i => arr.prob i * w i +
          (1 - arr.prob i) * omsr_patience_single_arrival_optimal_bestVal arr w (A.erase i) k)
        obtain ⟨L, hLnd, hLsub, hLlen, hLval⟩ := ih (A.erase i)
        refine ⟨i :: L, ?_, ?_, ?_, ?_⟩
        · rw [List.nodup_cons]
          exact ⟨fun hiL => Finset.notMem_erase i A (hLsub i hiL), hLnd⟩
        · intro j hj
          rw [List.mem_cons] at hj
          rcases hj with rfl | hj
          · exact hi
          · exact Finset.mem_of_mem_erase (hLsub j hj)
        · rw [List.length_cons]
          omega
        · rw [hbest, max_eq_right (le_of_lt hXpos)]
          simp only [probeValue, add_zero]
          rw [omsr_patience_single_arrival_optimal_probeValue_zero_indep arr w A (A.erase i) L,
            hLval, hsup]
    · refine ⟨[], List.nodup_nil, by simp, by simp, ?_⟩
      simp only [omsr_patience_single_arrival_optimal_bestVal, dif_neg hA]
      rfl

private theorem omsr_patience_single_arrival_optimal_optDP_all_matched {n m : ℕ} (w : Fin n → ℝ)
    (arrs : Fin m → OfflineArrival n) (hm : ∀ t, (arrs t).matched = true) :
    ∀ (fuel : ℕ) (S : Finset (Fin n)), optDP w fuel S arrs = 0 := by
  intro fuel
  induction fuel with
  | zero => intro S; rfl
  | succ fuel ih =>
    intro S
    simp only [optDP]
    rw [max_eq_left]
    refine Real.iSup_le (fun t => ?_) (le_refl 0)
    refine Real.iSup_le (fun i => ?_) (le_refl 0)
    refine Real.iSup_le (fun hcond => ?_) (le_refl 0)
    exact absurd (hm t) hcond.2.1

private theorem omsr_patience_single_arrival_optimal_optDP_single_le {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) :
    ∀ (fuel : ℕ) (S P : Finset (Fin n)),
      optDP (m := 1) w fuel S (fun _ => (⟨arr, P, false⟩ : OfflineArrival n))
        ≤ omsr_patience_single_arrival_optimal_bestVal arr w (S \ P) (arr.patience - P.card) := by
  intro fuel
  induction fuel with
  | zero =>
    intro S P
    simp only [optDP]
    exact omsr_patience_single_arrival_optimal_bestVal_nonneg arr w _ _
  | succ fuel ih =>
    intro S P
    simp only [optDP]
    refine max_le (omsr_patience_single_arrival_optimal_bestVal_nonneg arr w _ _) ?_
    refine Real.iSup_le (fun t => ?_)
      (omsr_patience_single_arrival_optimal_bestVal_nonneg arr w _ _)
    refine Real.iSup_le (fun i => ?_)
      (omsr_patience_single_arrival_optimal_bestVal_nonneg arr w _ _)
    refine Real.iSup_le (fun hcond => ?_)
      (omsr_patience_single_arrival_optimal_bestVal_nonneg arr w _ _)
    obtain ⟨hS, -, hP, hlt⟩ := hcond
    have hmemA : i ∈ S \ P := Finset.mem_sdiff.mpr ⟨hS, hP⟩
    have hA : (S \ P).Nonempty := ⟨i, hmemA⟩
    have hsucc : optDP w fuel (S.erase i)
        (fun j : Fin 1 => if j = t then (⟨arr, P, true⟩ : OfflineArrival n) else ⟨arr, P, false⟩) = 0 := by
      refine omsr_patience_single_arrival_optimal_optDP_all_matched w _ (fun j => ?_) fuel (S.erase i)
      rw [if_pos (Subsingleton.elim j t)]
    have hfail : (fun j : Fin 1 => if j = t then (⟨arr, insert i P, false⟩ : OfflineArrival n)
        else ⟨arr, P, false⟩) = fun _ => ⟨arr, insert i P, false⟩ := by
      funext j
      rw [if_pos (Subsingleton.elim j t)]
    rw [hsucc, hfail]
    have hIH := ih S (insert i P)
    have hbounded : arr.prob i * w i + (1 - arr.prob i) *
        omsr_patience_single_arrival_optimal_bestVal arr w (S \ insert i P) (arr.patience - (insert i P).card)
        ≤ omsr_patience_single_arrival_optimal_bestVal arr w (S \ P) (arr.patience - P.card) := by
      have hsdiff : S \ insert i P = (S \ P).erase i := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      have hcard : (insert i P).card = P.card + 1 := Finset.card_insert_of_notMem hP
      have hsub : arr.patience - (insert i P).card = (arr.patience - P.card) - 1 := by
        rw [hcard]; omega
      rw [hsdiff, hsub]
      have hstep := omsr_patience_single_arrival_optimal_bestVal_step_le arr w hA hmemA
        (arr.patience - P.card - 1)
      have hk : arr.patience - P.card - 1 + 1 = arr.patience - P.card := by omega
      rwa [hk] at hstep
    calc arr.prob i * (w i + 0) + (1 - arr.prob i) *
          optDP w fuel S (fun _ => (⟨arr, insert i P, false⟩ : OfflineArrival n))
        ≤ arr.prob i * w i + (1 - arr.prob i) *
          omsr_patience_single_arrival_optimal_bestVal arr w (S \ insert i P) (arr.patience - (insert i P).card) := by
          have hp1 : (0:ℝ) ≤ 1 - arr.prob i := by linarith [arr.prob_le_one i]
          have hmul := mul_le_mul_of_nonneg_left hIH hp1
          rw [add_zero]
          linarith
      _ ≤ omsr_patience_single_arrival_optimal_bestVal arr w (S \ P) (arr.patience - P.card) := hbounded

private noncomputable def omsr_patience_single_arrival_optimal_policy {n : ℕ}
    (arr : OMSRArrival n) (w : Fin n → ℝ) (S : Finset (Fin n)) : List (Fin n) :=
  (omsr_patience_single_arrival_optimal_bestVal_attained arr w S arr.patience).choose

private theorem omsr_patience_single_arrival_optimal_policy_spec {n : ℕ}
    (arr : OMSRArrival n) (w : Fin n → ℝ) (S : Finset (Fin n)) :
    (omsr_patience_single_arrival_optimal_policy arr w S).Nodup ∧
      (∀ i ∈ omsr_patience_single_arrival_optimal_policy arr w S, i ∈ S) ∧
      (omsr_patience_single_arrival_optimal_policy arr w S).length ≤ arr.patience ∧
      probeValue arr w (fun _ => 0) S (omsr_patience_single_arrival_optimal_policy arr w S)
        = omsr_patience_single_arrival_optimal_bestVal arr w S arr.patience :=
  (omsr_patience_single_arrival_optimal_bestVal_attained arr w S arr.patience).choose_spec

private theorem omsr_patience_single_arrival_optimal_policy_valid {n : ℕ}
    (arr : OMSRArrival n) (w : Fin n → ℝ) (S : Finset (Fin n)) :
    IsValidProbeSeq arr S (omsr_patience_single_arrival_optimal_policy arr w S) := by
  obtain ⟨h1, h2, h3, -⟩ := omsr_patience_single_arrival_optimal_policy_spec arr w S
  exact ⟨h1, h2, h3⟩

private theorem omsr_patience_single_arrival_optimal_policy_value {n : ℕ}
    (arr : OMSRArrival n) (w : Fin n → ℝ) (S : Finset (Fin n)) :
    probeValue arr w (fun _ => 0) S (omsr_patience_single_arrival_optimal_policy arr w S)
      = omsr_patience_single_arrival_optimal_bestVal arr w S arr.patience :=
  (omsr_patience_single_arrival_optimal_policy_spec arr w S).2.2.2

private theorem omsr_patience_single_arrival_optimal_offline_singleton_le {n : ℕ}
    (arr : OMSRArrival n) (w : Fin n → ℝ) :
    offlineOptValue w [arr] ≤ omsr_patience_single_arrival_optimal_bestVal arr w Finset.univ arr.patience := by
  have h : offlineOptValue w [arr] =
      optDP (m := 1) w n Finset.univ (fun _ => (⟨arr, ∅, false⟩ : OfflineArrival n)) := by
    simp [offlineOptValue]
  rw [h]
  have hb := omsr_patience_single_arrival_optimal_optDP_single_le arr w n Finset.univ (∅ : Finset (Fin n))
  simpa using hb

private theorem omsr_patience_single_arrival_optimal_online_singleton {n : ℕ}
    (arr : OMSRArrival n) (w : Fin n → ℝ) :
    onlinePolicyValue w (fun arr S => omsr_patience_single_arrival_optimal_policy arr w S)
      [arr] Finset.univ = omsr_patience_single_arrival_optimal_bestVal arr w Finset.univ arr.patience := by
  have h : onlinePolicyValue w (fun arr S => omsr_patience_single_arrival_optimal_policy arr w S)
      [arr] Finset.univ = probeValue arr w (fun _ => 0) Finset.univ
        (omsr_patience_single_arrival_optimal_policy arr w Finset.univ) := rfl
  rw [h]
  exact omsr_patience_single_arrival_optimal_policy_value arr w Finset.univ

private noncomputable def omsr_patience_single_arrival_optimal_randomized {n : ℕ} (w : Fin n → ℝ) :
    RandomizedOMSRPolicy n where
  Ω := PUnit
  mΩ := inferInstance
  μ := MeasureTheory.Measure.dirac PUnit.unit
  hμ := inferInstance
  policy := fun _ arr S => omsr_patience_single_arrival_optimal_policy arr w S
  valid := fun _ arr S => omsr_patience_single_arrival_optimal_policy_valid arr w S

private theorem omsr_patience_single_arrival_optimal_expected_eq {n : ℕ} (w : Fin n → ℝ)
    (arrs : List (OMSRArrival n)) :
    expectedOnlineValue w (omsr_patience_single_arrival_optimal_randomized w) arrs =
      onlinePolicyValue w (fun arr S => omsr_patience_single_arrival_optimal_policy arr w S) arrs Finset.univ := by
  unfold expectedOnlineValue omsr_patience_single_arrival_optimal_randomized
  simp only
  exact MeasureTheory.integral_dirac _ _

/-- Single-arrival instances achieve competitive ratio 1 against OPT. -/
theorem omsr_patience_single_arrival_optimal :
    ∀ (n : ℕ) (w : Fin n → ℝ), (∀ i, 0 ≤ w i) →
      ∃ R : RandomizedOMSRPolicy n,
        ∀ arrs : List (OMSRArrival n), arrs.length ≤ 1 →
          offlineOptValue w arrs ≤ expectedOnlineValue w R arrs := by
  intro n w hw
  refine ⟨omsr_patience_single_arrival_optimal_randomized w, ?_⟩
  intro arrs hlen
  rw [omsr_patience_single_arrival_optimal_expected_eq w arrs]
  rcases arrs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [offlineOptValue, onlinePolicyValue, optDP]
  · rw [omsr_patience_single_arrival_optimal_online_singleton a w]
    exact omsr_patience_single_arrival_optimal_offline_singleton_le a w
  · simp at hlen
