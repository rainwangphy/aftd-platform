import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsUniformBitPrior
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPriorUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionSenderUtility
import AFTD.Kb.GameTheoryEconomics.IsBitPrior
import AFTD.Kb.GameTheoryEconomics.IsSenderOptimalScheme
import AFTD.Kb.GameTheoryEconomics.IsObedientDirectScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrSchemeObedient
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverAddSenderLe
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtilityLe
import AFTD.Kb.GameTheoryEconomics.PersuasionMarginal

/-!
# persuasion_uniform_two_states_ratio_le

Topic: mechanism_design   Node: 0467c1766d99

Provenance: helper lemma. arXiv:2606.22226

For every finite type ι and every prior μ on ι → Bool that is uniform on 2 distinct states, the maximum receiver utility R_max(μ) is at most the prior utility R_0(μ).
-/

open Finset

noncomputable def persuasion_uniform_two_states_ratio_le_coupling {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : ι → Bool) (x y : ι → Bool) : ℝ :=
  if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then 1 / 2 else 0

lemma persuasion_uniform_two_states_ratio_le_coupling_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : ι → Bool) (x y : ι → Bool) :
    0 ≤ persuasion_uniform_two_states_ratio_le_coupling a b x y := by
  dsimp [persuasion_uniform_two_states_ratio_le_coupling]
  split_ifs <;> linarith

lemma persuasion_uniform_two_states_ratio_le_coupling_symm {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : ι → Bool) (x y : ι → Bool) :
    persuasion_uniform_two_states_ratio_le_coupling a b x y =
      persuasion_uniform_two_states_ratio_le_coupling a b y x := by
  dsimp [persuasion_uniform_two_states_ratio_le_coupling]
  by_cases h : (x = a ∧ y = b) ∨ (x = b ∧ y = a)
  · have h' : (y = a ∧ x = b) ∨ (y = b ∧ x = a) := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
      · left; exact ⟨rfl, rfl⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬ ((y = a ∧ x = b) ∨ (y = b ∧ x = a)) := by
      intro hc
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · apply h; right; exact ⟨rfl, rfl⟩
      · apply h; left; exact ⟨rfl, rfl⟩
    rw [if_neg h, if_neg h']

lemma persuasion_uniform_two_states_ratio_le_coupling_marginal {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) (a b : ι → Bool) (hab : a ≠ b)
    (hμ_supp : ∀ x, μ x ≠ 0 ↔ x = a ∨ x = b)
    (hμa : μ a = 1 / 2) (hμb : μ b = 1 / 2) (x : ι → Bool) :
    ∑ y, persuasion_uniform_two_states_ratio_le_coupling a b x y = μ x := by
  classical
  have hsupp_zero : ∀ z, z ≠ a → z ≠ b → μ z = 0 := by
    intro z hza hzb
    by_contra hz
    have := (hμ_supp z).mp hz
    tauto
  have hν_zero : ∀ y, y ≠ a → y ≠ b → persuasion_uniform_two_states_ratio_le_coupling a b x y = 0 := by
    intro y hya hyb
    dsimp [persuasion_uniform_two_states_ratio_le_coupling]
    split_ifs with h
    · rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> tauto
    · rfl
  have hsum : ∑ y, persuasion_uniform_two_states_ratio_le_coupling a b x y =
      persuasion_uniform_two_states_ratio_le_coupling a b x a +
      persuasion_uniform_two_states_ratio_le_coupling a b x b := by
    have hsub : ∑ y, persuasion_uniform_two_states_ratio_le_coupling a b x y =
        ∑ y ∈ ({a, b} : Finset (ι → Bool)), persuasion_uniform_two_states_ratio_le_coupling a b x y := by
      rw [← sum_subset (subset_univ _)]
      intro y _ hy
      rw [mem_insert, mem_singleton, not_or] at hy
      exact hν_zero y hy.1 hy.2
    rw [hsub, sum_insert (by simp [hab]), sum_singleton]
  rw [hsum]
  by_cases hxa : x = a
  · rw [hxa]
    dsimp [persuasion_uniform_two_states_ratio_le_coupling]
    have h1 : ¬ ((a = a ∧ a = b) ∨ (a = b ∧ a = a)) := by
      intro hc; rcases hc with ⟨-, hc⟩ | ⟨hc, -⟩ <;> exact hab hc
    have h2 : (a = a ∧ b = b) ∨ (a = b ∧ b = a) := Or.inl ⟨rfl, rfl⟩
    rw [if_neg h1, if_pos h2, zero_add, ← hxa, hxa, hμa]
  · by_cases hxb : x = b
    · rw [hxb]
      dsimp [persuasion_uniform_two_states_ratio_le_coupling]
      have h1 : (b = a ∧ a = b) ∨ (b = b ∧ a = a) := Or.inr ⟨rfl, rfl⟩
      have h2 : ¬ ((b = a ∧ b = b) ∨ (b = b ∧ b = a)) := by
        intro hc; rcases hc with ⟨hc, -⟩ | ⟨-, hc⟩ <;> exact hab (hc.symm)
      rw [if_pos h1, if_neg h2, add_zero, ← hxb, hxb, hμb]
    · dsimp [persuasion_uniform_two_states_ratio_le_coupling]
      have h1 : ¬ ((x = a ∧ a = b) ∨ (x = b ∧ a = a)) := by
        intro hc; rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> tauto
      have h2 : ¬ ((x = a ∧ b = b) ∨ (x = b ∧ b = a)) := by
        intro hc; rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> tauto
      rw [if_neg h1, if_neg h2, add_zero, hsupp_zero x hxa hxb]

lemma persuasion_uniform_two_states_ratio_le_coupling_sender_utility {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : ι → Bool) (hab : a ≠ b) :
    persuasion_sender_utility (persuasion_pair_or_scheme
      (persuasion_uniform_two_states_ratio_le_coupling a b)) =
      ∑ i, (if (a i || b i) = true then 1 else 0 : ℝ) := by
  classical
  rw [persuasion_pair_or_sender_utility]
  have h_inner : ∀ x, ∑ y, persuasion_uniform_two_states_ratio_le_coupling a b x y *
        ((univ.filter (fun i => (x i || y i) = true)).card : ℝ) =
      (if x = a then (1 / 2) * ((univ.filter (fun i => (a i || b i) = true)).card : ℝ) else 0) +
      (if x = b then (1 / 2) * ((univ.filter (fun i => (b i || a i) = true)).card : ℝ) else 0) := by
    intro x
    have hν_zero : ∀ y, y ≠ a → y ≠ b → persuasion_uniform_two_states_ratio_le_coupling a b x y = 0 := by
      intro y hya hyb
      dsimp [persuasion_uniform_two_states_ratio_le_coupling]
      split_ifs with h
      · rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> tauto
      · rfl
    have hsum : ∑ y, persuasion_uniform_two_states_ratio_le_coupling a b x y *
          ((univ.filter (fun i => (x i || y i) = true)).card : ℝ) =
        persuasion_uniform_two_states_ratio_le_coupling a b x a *
          ((univ.filter (fun i => (x i || a i) = true)).card : ℝ) +
        persuasion_uniform_two_states_ratio_le_coupling a b x b *
          ((univ.filter (fun i => (x i || b i) = true)).card : ℝ) := by
      have hsub : ∑ y, persuasion_uniform_two_states_ratio_le_coupling a b x y *
            ((univ.filter (fun i => (x i || y i) = true)).card : ℝ) =
          ∑ y ∈ ({a, b} : Finset (ι → Bool)), persuasion_uniform_two_states_ratio_le_coupling a b x y *
            ((univ.filter (fun i => (x i || y i) = true)).card : ℝ) := by
        rw [← sum_subset (subset_univ _)]
        intro y _ hy
        rw [mem_insert, mem_singleton, not_or] at hy
        rw [hν_zero y hy.1 hy.2, zero_mul]
      rw [hsub, sum_insert (by simp [hab]), sum_singleton]
    rw [hsum]
    by_cases hxa : x = a
    · rw [hxa]
      dsimp [persuasion_uniform_two_states_ratio_le_coupling]
      have h1 : ¬ ((a = a ∧ a = b) ∨ (a = b ∧ a = a)) := by
        intro hc; rcases hc with ⟨-, hc⟩ | ⟨hc, -⟩ <;> exact hab hc
      have h2 : (a = a ∧ b = b) ∨ (a = b ∧ b = a) := Or.inl ⟨rfl, rfl⟩
      rw [if_neg h1, if_pos h2, zero_mul, zero_add]
      rw [if_pos rfl, if_neg hab, add_zero]
    · by_cases hxb : x = b
      · rw [hxb]
        dsimp [persuasion_uniform_two_states_ratio_le_coupling]
        have h1 : (b = a ∧ a = b) ∨ (b = b ∧ a = a) := Or.inr ⟨rfl, rfl⟩
        have h2 : ¬ ((b = a ∧ b = b) ∨ (b = b ∧ b = a)) := by
          intro hc; rcases hc with ⟨hc, -⟩ | ⟨-, hc⟩ <;> exact hab (hc.symm)
        rw [if_pos h1, if_neg h2, zero_mul, add_zero]
        rw [if_neg (Ne.symm hab), if_pos rfl, zero_add]
      · dsimp [persuasion_uniform_two_states_ratio_le_coupling]
        have h1 : ¬ ((x = a ∧ a = b) ∨ (x = b ∧ a = a)) := by
          intro hc; rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> tauto
        have h2 : ¬ ((x = a ∧ b = b) ∨ (x = b ∧ b = a)) := by
          intro hc; rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> tauto
        rw [if_neg h1, if_neg h2, zero_mul, zero_mul, add_zero]
        rw [if_neg hxa, if_neg hxb, add_zero]
  simp_rw [h_inner]
  have houter : ∑ x, ((if x = a then (1 / 2) * ((univ.filter (fun i => (a i || b i) = true)).card : ℝ) else 0) +
      (if x = b then (1 / 2) * ((univ.filter (fun i => (b i || a i) = true)).card : ℝ) else 0)) =
      (1 / 2) * ((univ.filter (fun i => (a i || b i) = true)).card : ℝ) +
      (1 / 2) * ((univ.filter (fun i => (b i || a i) = true)).card : ℝ) := by
    rw [sum_add_distrib]
    congr 1
    · rw [← sum_subset (subset_univ {a})]
      · rw [sum_singleton, if_pos rfl]
      · intro x _ hx
        rw [mem_singleton] at hx
        rw [if_neg hx]
    · rw [← sum_subset (subset_univ {b})]
      · rw [sum_singleton, if_pos rfl]
      · intro x _ hx
        rw [mem_singleton] at hx
        rw [if_neg hx]
  rw [houter]
  have hsymm_card : (univ.filter (fun i => (b i || a i) = true)).card =
      (univ.filter (fun i => (a i || b i) = true)).card := by
    congr 1; ext i; simp [Bool.or_comm]
  rw [hsymm_card, ← add_mul]
  have hhalf : (1 / 2 : ℝ) + 1 / 2 = 1 := by ring
  rw [hhalf, one_mul]
  exact Finset.natCast_card_filter _ _

lemma persuasion_uniform_two_states_ratio_le_marginal {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) (a b : ι → Bool) (hab : a ≠ b)
    (hμ_supp : ∀ x, μ x ≠ 0 ↔ x = a ∨ x = b)
    (hμa : μ a = 1 / 2) (hμb : μ b = 1 / 2) (i : ι) :
    persuasion_marginal μ i = (if a i = true then 1 / 2 else 0) + (if b i = true then 1 / 2 else 0) := by
  classical
  dsimp [persuasion_marginal]
  have hzero : ∀ x, x ≠ a → x ≠ b → (if x i = true then μ x else 0) = 0 := by
    intro x hxa hxb
    by_contra h
    have hx : μ x ≠ 0 := by
      intro hμx
      rw [hμx, ite_self] at h
      exact h rfl
    have := (hμ_supp x).mp hx
    tauto
  have hsum : ∑ x, (if x i = true then μ x else 0) =
      (if a i = true then μ a else 0) + (if b i = true then μ b else 0) := by
    have hsub : ∑ x, (if x i = true then μ x else 0) =
        ∑ x ∈ ({a, b} : Finset (ι → Bool)), (if x i = true then μ x else 0) := by
      rw [← sum_subset (subset_univ _)]
      intro x _ hx
      rw [mem_insert, mem_singleton, not_or] at hx
      exact hzero x hx.1 hx.2
    rw [hsub, sum_insert (by simp [hab]), sum_singleton]
  rw [hsum, hμa, hμb]

open Finset in
/-- For 2 states (m = 1), the optimal receiver ratio is at most 1. -/
theorem persuasion_uniform_two_states_ratio_le
    (ι : Type) [Fintype ι] [DecidableEq ι] (μ : (ι → Bool) → ℝ)
    (hμ : is_uniform_bit_prior 2 μ) :
    persuasion_max_receiver_utility μ ≤ persuasion_prior_utility μ := by
  classical
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hμ.2.1
  have ha : a ∈ Finset.univ.filter (fun x => μ x ≠ 0) := by
    rw [hS]; simp
  have hb : b ∈ Finset.univ.filter (fun x => μ x ≠ 0) := by
    rw [hS]; simp
  rw [mem_filter] at ha hb
  have hμ_supp : ∀ x, μ x ≠ 0 ↔ x = a ∨ x = b := by
    intro x
    constructor
    · intro hx
      have hxS : x ∈ Finset.univ.filter (fun x => μ x ≠ 0) := by
        rw [mem_filter]; exact ⟨mem_univ _, hx⟩
      rw [hS, mem_insert, mem_singleton] at hxS
      exact hxS
    · rintro (rfl | rfl)
      · exact ha.2
      · exact hb.2
  have hμa : μ a = 1 / 2 := by
    have := hμ.2.2 a ha.2
    norm_num at this; exact this
  have hμb : μ b = 1 / 2 := by
    have := hμ.2.2 b hb.2
    norm_num at this; exact this
  set ν := persuasion_uniform_two_states_ratio_le_coupling a b
  have hν0 : ∀ x y, 0 ≤ ν x y := persuasion_uniform_two_states_ratio_le_coupling_nonneg a b
  have hνs : ∀ x y, ν x y = ν y x := persuasion_uniform_two_states_ratio_le_coupling_symm a b
  have hνμ : ∀ x, ∑ y, ν x y = μ x :=
    persuasion_uniform_two_states_ratio_le_coupling_marginal μ a b hab hμ_supp hμa hμb
  have hobs := persuasion_pair_or_scheme_obedient μ ν hν0 hνs hνμ
  have hSor := persuasion_uniform_two_states_ratio_le_coupling_sender_utility a b hab
  have h_marg := persuasion_uniform_two_states_ratio_le_marginal μ a b hab hμ_supp hμa hμb
  have hp := persuasion_marginal_mem_Icc μ hμ.1
  have hR0 : 0 ≤ persuasion_prior_utility μ :=
    sum_nonneg fun i _ => le_max_of_le_left (hp i).1
  have key : ∀ q, is_sender_optimal_scheme μ q →
      persuasion_receiver_utility q ≤ persuasion_prior_utility μ := by
    rintro q ⟨hq, hopt⟩
    have h1 := persuasion_receiver_add_sender_le μ hμ.1.2 q hq
    have h2 := hopt _ hobs
    rw [hSor] at h2
    have hc : (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
    have h3 : (Fintype.card ι : ℝ) + ∑ i, persuasion_marginal μ i -
        ∑ i, (if (a i || b i) = true then 1 else 0 : ℝ) ≤
        persuasion_prior_utility μ := by
      rw [hc, persuasion_prior_utility, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_le_sum
      intro i _
      rw [h_marg i]
      cases a i <;> cases b i <;> simp
    linarith
  apply Real.sSup_le
  · rintro r ⟨q, hq, rfl⟩
    exact key q hq
  · exact hR0
