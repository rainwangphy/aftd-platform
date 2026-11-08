import AFTD.Prelude
import AFTD.Kb.Tcs.OMSRArrival
import AFTD.Kb.Tcs.OfflineArrival
import AFTD.Kb.Tcs.ProbeValue
import AFTD.Kb.Tcs.OptDP
import AFTD.Kb.Tcs.OfflineOptValue
import AFTD.Kb.Tcs.IsValidProbeSeq

/-!
# omsr_single_arrival_optimal_probeSeq_exists

Topic: online_algorithms   Node: ad111a99a932

Provenance: helper lemma. step towards omsr_patience_single_arrival_optimal

For any resource weights w ≥ 0 and single arrival arr, there exists a valid probe sequence L from the full resource set univ whose probe value achieves at least offlineOptValue w [arr].
-/

noncomputable def omsr_single_arrival_optimal_probeSeq_exists_bestVal {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) : Finset (Fin n) → ℕ → ℝ
  | _, 0 => 0
  | A, k + 1 =>
      if h : A.Nonempty then
        max 0 (A.sup' h (fun i => arr.prob i * w i + (1 - arr.prob i) *
          omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w (A.erase i) k))
      else 0

theorem omsr_single_arrival_optimal_probeSeq_exists_bestVal_nonneg {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) (A : Finset (Fin n)) (k : ℕ) :
    0 ≤ omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w A k := by
  induction k generalizing A with
  | zero => simp [omsr_single_arrival_optimal_probeSeq_exists_bestVal]
  | succ k ih =>
    by_cases h : A.Nonempty
    · rw [omsr_single_arrival_optimal_probeSeq_exists_bestVal, dif_pos h]
      exact le_max_left _ _
    · rw [omsr_single_arrival_optimal_probeSeq_exists_bestVal, dif_neg h]

theorem omsr_single_arrival_optimal_probeSeq_exists_bestVal_step_le {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) {A : Finset (Fin n)} (h : A.Nonempty) {i : Fin n} (hi : i ∈ A) (k : ℕ) :
    arr.prob i * w i + (1 - arr.prob i) *
      omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w (A.erase i) k
      ≤ omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w A (k + 1) := by
  rw [omsr_single_arrival_optimal_probeSeq_exists_bestVal, dif_pos h]
  exact le_trans (Finset.le_sup' (fun i => arr.prob i * w i + (1 - arr.prob i) *
      omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w (A.erase i) k) hi) (le_max_right _ _)

theorem omsr_single_arrival_optimal_probeSeq_exists_probeValue_zero_indep {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) (S S' : Finset (Fin n)) (L : List (Fin n)) :
    probeValue arr w (fun _ => (0:ℝ)) S L = probeValue arr w (fun _ => (0:ℝ)) S' L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [probeValue]
    rw [ih]

theorem omsr_single_arrival_optimal_probeSeq_exists_bestVal_attained {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) (A : Finset (Fin n)) (k : ℕ) :
    ∃ L : List (Fin n), L.Nodup ∧ (∀ i ∈ L, i ∈ A) ∧ L.length ≤ k ∧
      probeValue arr w (fun _ => 0) A L = omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w A k := by
  induction k generalizing A with
  | zero => exact ⟨[], List.nodup_nil, by simp, by simp, rfl⟩
  | succ k ih =>
    by_cases hA : A.Nonempty
    · have hbest : omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w A (k + 1)
          = max 0 (A.sup' hA (fun i => arr.prob i * w i + (1 - arr.prob i) *
              omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w (A.erase i) k)) := by
        simp only [omsr_single_arrival_optimal_probeSeq_exists_bestVal, dif_pos hA]
      by_cases hX : A.sup' hA (fun i => arr.prob i * w i + (1 - arr.prob i) *
          omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w (A.erase i) k) ≤ 0
      · refine ⟨[], List.nodup_nil, by simp, by simp, ?_⟩
        rw [hbest, max_eq_left hX]
        rfl
      · have hXpos : 0 < A.sup' hA (fun i => arr.prob i * w i + (1 - arr.prob i) *
            omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w (A.erase i) k) := not_le.mp hX
        obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' hA (fun i => arr.prob i * w i +
          (1 - arr.prob i) * omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w (A.erase i) k)
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
          rw [omsr_single_arrival_optimal_probeSeq_exists_probeValue_zero_indep arr w A (A.erase i) L,
            hLval, hsup]
    · refine ⟨[], List.nodup_nil, by simp, by simp, ?_⟩
      simp only [omsr_single_arrival_optimal_probeSeq_exists_bestVal, dif_neg hA]
      rfl

theorem omsr_single_arrival_optimal_probeSeq_exists_optDP_all_matched {n m : ℕ} (w : Fin n → ℝ)
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
    exact absurd (hm t) (by simp [hcond.2.1])

theorem omsr_single_arrival_optimal_probeSeq_exists_optDP_single_le {n : ℕ} (arr : OMSRArrival n)
    (w : Fin n → ℝ) :
    ∀ (fuel : ℕ) (S P : Finset (Fin n)),
      optDP (m := 1) w fuel S (fun _ => (⟨arr, P, false⟩ : OfflineArrival n))
        ≤ omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w (S \ P) (arr.patience - P.card) := by
  intro fuel
  induction fuel with
  | zero =>
    intro S P
    simp only [optDP]
    exact omsr_single_arrival_optimal_probeSeq_exists_bestVal_nonneg arr w _ _
  | succ fuel ih =>
    intro S P
    simp only [optDP]
    refine max_le (omsr_single_arrival_optimal_probeSeq_exists_bestVal_nonneg arr w _ _) ?_
    refine Real.iSup_le (fun t => ?_)
      (omsr_single_arrival_optimal_probeSeq_exists_bestVal_nonneg arr w _ _)
    refine Real.iSup_le (fun i => ?_)
      (omsr_single_arrival_optimal_probeSeq_exists_bestVal_nonneg arr w _ _)
    refine Real.iSup_le (fun hcond => ?_)
      (omsr_single_arrival_optimal_probeSeq_exists_bestVal_nonneg arr w _ _)
    obtain ⟨hS, -, hP, hlt⟩ := hcond
    have hmemA : i ∈ S \ P := Finset.mem_sdiff.mpr ⟨hS, hP⟩
    have hA : (S \ P).Nonempty := ⟨i, hmemA⟩
    have hsucc_fun : (fun j : Fin 1 => if j = t then ({ arrival := arr, probed := P, matched := true } : OfflineArrival n)
        else { arrival := arr, probed := P, matched := false }) =
        fun _ => ({ arrival := arr, probed := P, matched := true } : OfflineArrival n) := by
      ext j; rw [Subsingleton.elim j t, if_pos rfl]
    have hsucc : optDP w fuel (S.erase i)
        (fun j => if j = t then ({ arrival := arr, probed := P, matched := true } : OfflineArrival n)
        else { arrival := arr, probed := P, matched := false }) = 0 := by
      rw [hsucc_fun]
      apply omsr_single_arrival_optimal_probeSeq_exists_optDP_all_matched
      intro j
      rfl
    have hfail_fun : (fun j : Fin 1 => if j = t then ({ arrival := arr, probed := insert i P, matched := false } : OfflineArrival n)
        else { arrival := arr, probed := P, matched := false }) =
        fun _ => ({ arrival := arr, probed := insert i P, matched := false } : OfflineArrival n) := by
      ext j; rw [Subsingleton.elim j t, if_pos rfl]
    have hfail : optDP w fuel S
        (fun j => if j = t then ({ arrival := arr, probed := insert i P, matched := false } : OfflineArrival n)
        else { arrival := arr, probed := P, matched := false })
        ≤ omsr_single_arrival_optimal_probeSeq_exists_bestVal arr w (S \ insert i P) (arr.patience - (insert i P).card) := by
      rw [hfail_fun]
      exact ih S (insert i P)
    have hcard : (insert i P).card = P.card + 1 := Finset.card_insert_of_notMem hP
    have hsdiff : S \ insert i P = (S \ P).erase i := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, Finset.mem_erase]
      tauto
    rw [hsucc]
    rw [hsdiff, hcard] at hfail
    have hbounded := omsr_single_arrival_optimal_probeSeq_exists_bestVal_step_le arr w hA hmemA (arr.patience - (P.card + 1))
    have hp1 : (0:ℝ) ≤ 1 - arr.prob i := by linarith [arr.prob_le_one i]
    have hmul := mul_le_mul_of_nonneg_left hfail hp1
    rw [add_zero]
    have heq : arr.patience - (P.card + 1) + 1 = arr.patience - P.card := by omega
    rw [heq] at hbounded
    linarith

theorem omsr_single_arrival_optimal_probeSeq_exists (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (arr : OMSRArrival n) :
    ∃ L : List (Fin n), IsValidProbeSeq arr Finset.univ L ∧ offlineOptValue w [arr] ≤ probeValue arr w (fun _ => 0) Finset.univ L := by
  obtain ⟨L, hnd, hsub, hlen, hval⟩ := omsr_single_arrival_optimal_probeSeq_exists_bestVal_attained arr w Finset.univ arr.patience
  refine ⟨L, ⟨hnd, hsub, hlen⟩, ?_⟩
  rw [hval]
  have hopt : offlineOptValue w [arr] = optDP (m := 1) w (1 * n) Finset.univ (fun _ => ⟨arr, ∅, false⟩) := by
    dsimp [offlineOptValue]
    congr 1
    ext idx
    have : idx = 0 := Subsingleton.elim idx 0
    subst this
    rfl
  rw [hopt]
  have hle := omsr_single_arrival_optimal_probeSeq_exists_optDP_single_le arr w (1 * n) Finset.univ ∅
  simp only [Finset.sdiff_empty, Finset.card_empty, Nat.sub_zero] at hle
  exact hle
