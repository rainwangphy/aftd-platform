import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EqualMarginalBalancedHighCountAllocations
import AFTD.Kb.GameTheoryEconomics.BalancedHighCountChoreMmsBound
import AFTD.Kb.GameTheoryEconomics.IsEqualMarginalLottery
import AFTD.Kb.GameTheoryEconomics.IsScaledBivaluedChores
import AFTD.Kb.GameTheoryEconomics.IsExPostAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.IsAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# all_agent_bivalued_equal_marginal_divisible_chores

Topic: fair_division   Node: b22996cfc8a9

Provenance: original. Related work: OP-1112; compare the equal-marginal sorted-slot mechanism in arXiv:2609.35280, Lemma 3.1, and the two-agent bound in https://rainwangphy.github.io/aftd-platform/blog/2026-11-06-op-1112/.

For every n at least two and k at least two, any common ratio r at least one, and any n-agent scaled bivalued additive cost profile on n*k chores, there is a nonnegative weight for every complete allocation, with all weights summing to 1, such that each chore is assigned to each agent with marginal probability 1/n and every allocation with positive weight gives each agent at most (r+1)/2 times her n-agent chore maximin share.
-/

theorem all_agent_bivalued_equal_marginal_divisible_chores (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (r : ℝ) (hr : 1 ≤ r) (c : Fin n → Fin (n*k) → ℝ) (hc : is_scaled_bivalued_chores r c) : ∃ p ∈ stdSimplex ℝ (Fin (n*k) → Fin n), is_equal_marginal_lottery p ∧ is_ex_post_alpha_mms_chores ((r+1)/2) c p := by
  open Finset in
  rcases hc with ⟨a, ha_pos, ha_val⟩
  let H : Fin n → Finset (Fin (n*k)) := fun i => univ.filter (fun g => c i g = r * a i)
  obtain ⟨F, hF_bij, hF_prop⟩ := equal_marginal_balanced_high_count_allocations n k hn hk H
  let p : (Fin (n*k) → Fin n) → ℝ := fun σ => ∑ t : Fin n, if σ = F t then 1 / (n : ℝ) else 0
  have hn_pos : (n : ℝ) ≠ 0 := by positivity
  have hp_simp : p ∈ stdSimplex ℝ (Fin (n*k) → Fin n) := by
    dsimp [stdSimplex, p]
    constructor
    · intro σ
      apply sum_nonneg
      intro t _
      split_ifs
      · positivity
      · rfl
    · rw [sum_comm]
      have h1 : ∀ t : Fin n, (∑ x : Fin (n * k) → Fin n, if x = F t then 1 / (n : ℝ) else 0) = 1 / (n : ℝ) := by
        intro t
        rw [sum_ite_eq']
        simp
      simp_rw [h1]
      simp [hn_pos]
  refine ⟨p, hp_simp, ?_, ?_⟩
  · intro g i
    dsimp [p]
    have h_split : ∀ σ : Fin (n * k) → Fin n,
        (if σ g = i then (∑ t : Fin n, if σ = F t then 1 / (n : ℝ) else 0) else 0) =
        ∑ t : Fin n, (if σ = F t then (if F t g = i then 1 / (n : ℝ) else 0) else 0) := by
      intro σ
      have h1 : (if σ g = i then (∑ t : Fin n, if σ = F t then 1 / (n : ℝ) else 0) else 0) =
          ∑ t : Fin n, (if σ g = i then (if σ = F t then 1 / (n : ℝ) else 0) else 0) := by
        split_ifs with hg
        · rfl
        · simp
      rw [h1]
      congr 1; ext t
      by_cases heq : σ = F t
      · subst heq
        split_ifs <;> rfl
      · simp [heq]
    simp_rw [h_split]
    rw [sum_comm]
    have h_inner : ∀ t : Fin n, (∑ σ : Fin (n * k) → Fin n, if σ = F t then (if F t g = i then 1 / (n : ℝ) else 0) else 0) =
        if F t g = i then 1 / (n : ℝ) else 0 := by
      intro t
      rw [sum_ite_eq']
      simp
    simp_rw [h_inner]
    let e := Equiv.ofBijective (fun t => F t g) (hF_bij g)
    have h := (Equiv.sum_comp e (fun x => if x = i then 1 / (n : ℝ) else 0)).symm
    have he : ∀ t, e t = F t g := fun _ => rfl
    simp_rw [he] at h
    rw [← h, sum_ite_eq']
    simp
  · intro σ hσ
    have h_ex : ∃ t : Fin n, σ = F t := by
      by_contra h_not
      have h_zero : p σ = 0 := by
        dsimp [p]
        have : ∀ t : Fin n, (if σ = F t then 1 / (n : ℝ) else 0) = 0 := by
          intro t
          have : ¬ σ = F t := fun h => h_not ⟨t, h⟩
          rw [if_neg this]
        simp_rw [this, sum_const_zero]
      linarith
    rcases h_ex with ⟨t, rfl⟩
    intro i
    have h_inter : bundle_of (F t) i ∩ univ.filter (fun g => c i g = r * a i) =
        (bundle_of (F t) i).filter (fun g => c i g = r * a i) := by
      ext g
      simp
    have hh : n * ((bundle_of (F t) i).filter (fun g => c i g = r * a i)).card ≤
        (univ.filter (fun g => c i g = r * a i)).card + n - 1 := by
      rw [← h_inter]
      exact (hF_prop t i).2
    exact balanced_high_count_chore_mms_bound n k hn hk r hr (a i) (ha_pos i) (c i) (ha_val i)
      (bundle_of (F t) i) (hF_prop t i).1 hh
