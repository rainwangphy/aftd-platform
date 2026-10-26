import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.PandoraCappedSurplus
import AFTD.Kb.Tcs.PandoraDeadlineFeasible
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.PandoraDeadlineFeasibleEmpty

/-!
# pandora_exists_balancing_threshold

Topic: online_algorithms   Node: f5d6c1f577ac

Provenance: helper lemma. Helper for op184_partially_adaptive_half_approximation: arXiv:2610.13775 Section 3, Theorem 1 proof (choice of the balancing threshold t*)

There is a threshold t >= 0 at which the maximum total capped surplus over deadline-feasible sets equals t, attained by some feasible set.
-/

lemma pandora_exists_balancing_threshold_continuous_finset_sup' {α β γ : Type*}
    [TopologicalSpace α] [LinearOrder β] [TopologicalSpace β] [ContinuousSup β]
    (s : Finset γ) (hs : s.Nonempty) (f : γ → α → β)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun a => s.sup' hs (fun i => f i a)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [Finset.sup'_singleton]
    apply hf a (Finset.mem_singleton_self a)
  | cons a t ha ht ih =>
    simp only [Finset.sup'_cons ht]
    apply Continuous.sup
    · apply hf a (Finset.mem_cons_self a t)
    · apply ih
      intro i hi
      apply hf i (Finset.mem_cons_of_mem hi)

lemma pandora_exists_balancing_threshold_antitone_finset_sup' {α β γ : Type*}
    [LinearOrder β] [Preorder α]
    (s : Finset γ) (hs : s.Nonempty) (f : γ → α → β)
    (hf : ∀ i ∈ s, Antitone (f i)) :
    Antitone (fun a => s.sup' hs (fun i => f i a)) := by
  intro t1 t2 hle
  apply Finset.sup'_le
  intro i hi
  have hle' := hf i hi hle
  have hsup := Finset.le_sup' (fun j => f j t1) hi
  exact le_trans hle' hsup

lemma pandora_exists_balancing_threshold_capped_surplus_continuous (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (i : Fin inst.n) :
    Continuous (pandora_capped_surplus inst r i) := by
  unfold pandora_capped_surplus
  continuity

lemma pandora_exists_balancing_threshold_capped_surplus_sum_continuous (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (S : Finset (Fin inst.n)) :
    Continuous (fun t => ∑ i ∈ S, pandora_capped_surplus inst r i t) := by
  apply continuous_finsetSum
  intro i _
  exact pandora_exists_balancing_threshold_capped_surplus_continuous inst r i

lemma pandora_exists_balancing_threshold_capped_surplus_antitone (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (i : Fin inst.n) :
    Antitone (pandora_capped_surplus inst r i) := by
  intro t1 t2 hle
  dsimp [pandora_capped_surplus]
  apply Finset.sum_le_sum
  intro v hv
  apply mul_le_mul_of_nonneg_left
  · apply max_le_max
    · linarith
    · rfl
  · exact (inst.dist i).prob_nonneg v hv

lemma pandora_exists_balancing_threshold_capped_surplus_sum_antitone (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (S : Finset (Fin inst.n)) :
    Antitone (fun t => ∑ i ∈ S, pandora_capped_surplus inst r i t) := by
  intro t1 t2 hle
  apply Finset.sum_le_sum
  intro i _
  exact pandora_exists_balancing_threshold_capped_surplus_antitone inst r i hle

theorem pandora_exists_balancing_threshold (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ S : Finset (Fin inst.n), pandora_deadline_feasible inst S ∧
      ∑ i ∈ S, pandora_capped_surplus inst r i t = t ∧
      ∀ S' : Finset (Fin inst.n), pandora_deadline_feasible inst S' →
        ∑ i ∈ S', pandora_capped_surplus inst r i t ≤ t := by
  classical
  let F : Finset (Finset (Fin inst.n)) := Finset.filter (pandora_deadline_feasible inst) Finset.univ
  have hF_mem_empty : ∅ ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ ∅, pandora_deadline_feasible_empty inst⟩
  have hF : F.Nonempty := ⟨∅, hF_mem_empty⟩
  let term (S : Finset (Fin inst.n)) (t : ℝ) : ℝ := ∑ i ∈ S, pandora_capped_surplus inst r i t
  let W (t : ℝ) : ℝ := F.sup' hF (fun S => term S t)
  have hW_cont : Continuous W :=
    pandora_exists_balancing_threshold_continuous_finset_sup' F hF term
      (fun S _ => pandora_exists_balancing_threshold_capped_surplus_sum_continuous inst r S)
  have hW_anti : Antitone W :=
    pandora_exists_balancing_threshold_antitone_finset_sup' F hF term
      (fun S _ => pandora_exists_balancing_threshold_capped_surplus_sum_antitone inst r S)
  let g (t : ℝ) : ℝ := W t - t
  have hg_cont : Continuous g := hW_cont.sub continuous_id
  let b := W 0 + 1
  have hW0_nonneg : 0 ≤ W 0 := by
    have hzero : term ∅ 0 = 0 := Finset.sum_empty
    have := Finset.le_sup' (fun S => term S 0) hF_mem_empty
    linarith
  have hab : 0 ≤ b := by linarith
  have hga : 0 ≤ g 0 := by
    dsimp [g]
    linarith
  have hgb : g b ≤ 0 := by
    dsimp [g, b]
    have := hW_anti hab
    linarith
  have h_mem : (0 : ℝ) ∈ Set.Icc (g b) (g 0) := ⟨hgb, hga⟩
  have hivt := intermediate_value_Icc' hab hg_cont.continuousOn h_mem
  rcases hivt with ⟨t, ht_icc, ht_eq⟩
  have ht_nonneg : 0 ≤ t := ht_icc.1
  have hWt : W t = t := by
    dsimp [g] at ht_eq
    linarith
  obtain ⟨S, hS_mem, hS_eq⟩ := Finset.exists_mem_eq_sup' hF (fun S' => term S' t)
  rw [Finset.mem_filter] at hS_mem
  refine ⟨t, ht_nonneg, S, hS_mem.2, ?_, ?_⟩
  · change term S t = t
    rw [← hS_eq]
    exact hWt
  · intro S' hS'
    have hS'_mem : S' ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ S', hS'⟩
    have hle := Finset.le_sup' (fun S'' => term S'' t) hS'_mem
    exact le_trans hle (le_of_eq hWt)
