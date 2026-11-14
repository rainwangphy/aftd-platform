import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.UniformBivaluedObstructionCost
import AFTD.Kb.GameTheoryEconomics.IsEqualMarginalLottery
import AFTD.Kb.GameTheoryEconomics.IsExPostAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.IsAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare

/-!
# uniform_bivalued_obstruction_no_equal_marginal_exact_mms

Topic: fair_division   Node: 29d71a83e3d0

Provenance: formalization of a published result. Source: OP-1697

For every integer t at least 2 and every real ratio r strictly between 1 + 1/t and 1 + 1/(t-1), the instance with 4t chores where agent 0 assigns cost 1 to all chores and agent 1 assigns cost r to 2t - 1 chores and cost 1 to 2t + 1 chores admits no equal-marginal exact-MMS lottery.
-/

open Finset

/-- Complement count of the "first m" elements of `Fin n`. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_card_filter_fin_not_lt (n m : ℕ) :
    (Finset.univ.filter (fun i : Fin n => ¬ (i:ℕ) < m)).card = n - min n m := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun i : Fin n => (i:ℕ) < m)
  rw [Finset.card_univ, Fintype.card_fin, Fin.card_filter_val_lt] at h
  omega

/-- The chore maximin share is at most the maximum bundle cost of any fixed partition. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_mms_le_of_partition {m n : ℕ}
    [NeZero n] (u : Fin m → ℝ) (P : Fin m → Fin n) (C : ℝ)
    (h : ∀ k, additive_valuation u (bundle_of P k) ≤ C) : chore_maximin_share n u ≤ C := by
  unfold chore_maximin_share
  exact ciInf_le_of_le (Set.finite_range _).bddBelow P (ciSup_le h)

/-- For unit costs the additive valuation of a bundle is its cardinality. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_additive_valuation_one (m : ℕ)
    (S : Finset (Fin m)) :
    additive_valuation (fun _ => (1:ℝ)) S = (S.card : ℝ) := by
  simp [additive_valuation]

/-- The two bundles of a two-agent allocation partition all chores. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_card_bundle_zero_add_one {m : ℕ}
    (σ : Fin m → Fin 2) : (bundle_of σ 0).card + (bundle_of σ 1).card = m := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (p := fun g : Fin m => σ g = 0)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have e : Finset.univ.filter (fun g : Fin m => ¬ σ g = 0) = bundle_of σ 1 := by
    simp only [bundle_of]
    apply Finset.filter_congr
    intro g _
    constructor
    · intro hg
      have h2 : σ g = 0 ∨ σ g = 1 := by
        have hv : (σ g : ℕ) < 2 := (σ g).isLt
        omega
      rcases h2 with h' | h'
      · exact absurd h' hg
      · exact h'
    · intro hg h0
      rw [h0] at hg
      simp at hg
  rw [e] at h
  have h0 : bundle_of σ 0 = Finset.univ.filter (fun g : Fin m => σ g = 0) := rfl
  rw [h0]
  omega

/-- In an equal-marginal lottery the expected number of chores of `A` given to agent `i` is `|A|/2`. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_sum_p_mul_card_inter {m : ℕ}
    (p : (Fin m → Fin 2) → ℝ) (hp : is_equal_marginal_lottery p) (i : Fin 2) (A : Finset (Fin m)) :
    ∑ σ, p σ * (((bundle_of σ i) ∩ A).card : ℝ) = (A.card : ℝ) / 2 := by
  have hcard (σ : Fin m → Fin 2) :
      (∑ g ∈ A, if σ g = i then (1:ℝ) else 0) = (((bundle_of σ i) ∩ A).card : ℝ) := by
    have hset : A.filter (fun g => σ g = i) = (bundle_of σ i) ∩ A := by
      ext g
      simp [bundle_of, Finset.mem_filter, and_comm]
    rw [Finset.sum_boole, hset]
  calc ∑ σ, p σ * (((bundle_of σ i) ∩ A).card : ℝ)
      = ∑ σ, p σ * ∑ g ∈ A, (if σ g = i then (1:ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [hcard σ]
    _ = ∑ σ, ∑ g ∈ A, p σ * (if σ g = i then (1:ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [Finset.mul_sum]
    _ = ∑ g ∈ A, ∑ σ, p σ * (if σ g = i then (1:ℝ) else 0) := Finset.sum_comm
    _ = ∑ g ∈ A, ∑ σ, (if σ g = i then p σ else 0) := by
        apply Finset.sum_congr rfl
        intro g _
        apply Finset.sum_congr rfl
        intro σ _
        by_cases h : σ g = i <;> simp [h]
    _ = ∑ g ∈ A, (1/2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [hp g i]
        norm_num
    _ = (A.card : ℝ) / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- Agent 1's cost of a chore: `r` on the high chores, `1` elsewhere. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_cost_one_apply (t : ℕ) (r : ℝ)
    (g : Fin (4*t)) :
    uniform_bivalued_obstruction_cost t r 1 g = if (g:ℕ) < 2*t-1 then r else 1 := by
  simp [uniform_bivalued_obstruction_cost]

/-- Agent 0's cost is one on every chore. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_cost_zero_apply (t : ℕ) (r : ℝ)
    (g : Fin (4*t)) : uniform_bivalued_obstruction_cost t r 0 g = 1 := by
  simp [uniform_bivalued_obstruction_cost]

/-- Agent 1's cost of a bundle: its size plus `(r-1)` times its number of high chores. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_cost_one_decomp {t : ℕ} (r : ℝ)
    (σ : Fin (4*t) → Fin 2) (H : Finset (Fin (4*t)))
    (hH : H = Finset.univ.filter (fun g : Fin (4*t) => (g:ℕ) < 2*t-1)) :
    additive_valuation (uniform_bivalued_obstruction_cost t r 1) (bundle_of σ 1)
      = ((bundle_of σ 1).card : ℝ)
        + (r - 1) * (((bundle_of σ 1) ∩ H).card : ℝ) := by
  have hpt : ∀ g : Fin (4*t), uniform_bivalued_obstruction_cost t r 1 g
      = 1 + (r-1) * (if (g:ℕ) < 2*t-1 then (1:ℝ) else 0) := by
    intro g
    rw [uniform_bivalued_obstruction_no_equal_marginal_exact_mms_cost_one_apply]
    by_cases h : (g:ℕ) < 2*t-1 <;> simp [h]
  rw [additive_valuation]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have hset : (bundle_of σ 1).filter (fun g : Fin (4*t) => (g:ℕ) < 2*t-1)
      = (bundle_of σ 1) ∩ H := by
    rw [hH]
    ext g
    simp [Finset.mem_filter, and_comm]
  rw [← hset, ← Finset.sum_boole]

/-- For `4t` unit-cost chores and two agents the maximin share is at most `2t`. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_mms_const_one_four_mul (t : ℕ)
    (ht : 2 ≤ t) : chore_maximin_share 2 (fun _ : Fin (4*t) => (1:ℝ)) ≤ 2 * t := by
  set P : Fin (4*t) → Fin 2 := fun g => if (g:ℕ) < 2*t then 0 else 1 with hP
  refine uniform_bivalued_obstruction_no_equal_marginal_exact_mms_mms_le_of_partition
    (fun _ => (1:ℝ)) P (2*t) ?_
  have h0 : (bundle_of P 0).card = 2*t := by
    have : bundle_of P 0 = Finset.univ.filter (fun g : Fin (4*t) => (g:ℕ) < 2*t) := by
      simp only [bundle_of, hP]
      apply Finset.filter_congr
      intro g _
      by_cases h : (g:ℕ) < 2*t <;> simp [h]
    rw [this, Fin.card_filter_val_lt, min_eq_right (by omega)]
  have h1 : (bundle_of P 1).card = 2*t := by
    have : bundle_of P 1 = Finset.univ.filter (fun g : Fin (4*t) => ¬ (g:ℕ) < 2*t) := by
      simp only [bundle_of, hP]
      apply Finset.filter_congr
      intro g _
      by_cases h : (g:ℕ) < 2*t <;> simp [h]
    rw [this, uniform_bivalued_obstruction_no_equal_marginal_exact_mms_card_filter_fin_not_lt,
      min_eq_right (by omega)]
    omega
  intro k
  rw [uniform_bivalued_obstruction_no_equal_marginal_exact_mms_additive_valuation_one]
  have hb : (bundle_of P k).card = 2*t := by
    fin_cases k
    · simpa using h0
    · simpa using h1
  rw [hb]
  push_cast
  linarith

/-- Agent 1's maximin share in this instance is at most `t*(1+r)`: put all high chores in one
bundle and all low chores in the other. -/
lemma uniform_bivalued_obstruction_no_equal_marginal_exact_mms_mms_cost_one_le (t : ℕ) (ht : 2 ≤ t)
    (r : ℝ) (hr_lo : 1 + 1 / (t : ℝ) < r) (hr_hi : r < 1 + 1 / ((t - 1 : ℕ) : ℝ)) :
    chore_maximin_share 2 (uniform_bivalued_obstruction_cost t r 1) < t * (1 + r) := by
  have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    norm_num
  have htR : (2:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hpos : (0:ℝ) < (t:ℝ) - 1 := by linarith
  have htpos : (0:ℝ) < (t:ℝ) := by linarith
  have harith1 : (2*(t:ℝ) - 1) * r < t * (1 + r) := by
    have h1 : r - 1 < 1 / ((t:ℝ) - 1) := by rw [← hcast]; linarith
    rw [lt_div_iff₀ hpos] at h1
    nlinarith
  have harith2 : 2*(t:ℝ) + 1 < t * (1 + r) := by
    have h1 : (1/(t:ℝ)) * (t:ℝ) = 1 := by field_simp
    nlinarith [hr_lo, htpos]
  set H : Finset (Fin (4*t)) := Finset.univ.filter (fun g : Fin (4*t) => (g:ℕ) < 2*t-1) with hH
  have hHcard : H.card = 2*t-1 := by
    rw [hH, Fin.card_filter_val_lt, min_eq_right (by omega)]
  set P : Fin (4*t) → Fin 2 := fun g => if (g:ℕ) < 2*t-1 then 0 else 1 with hP
  have hb0 : bundle_of P 0 = H := by
    simp only [bundle_of, hP, hH]
    apply Finset.filter_congr
    intro g _
    by_cases h : (g:ℕ) < 2*t-1 <;> simp [h]
  have hb1 : bundle_of P 1 = Finset.univ.filter (fun g : Fin (4*t) => ¬ (g:ℕ) < 2*t-1) := by
    simp only [bundle_of, hP]
    apply Finset.filter_congr
    intro g _
    by_cases h : (g:ℕ) < 2*t-1 <;> simp [h]
  have hc0 : additive_valuation (uniform_bivalued_obstruction_cost t r 1) (bundle_of P 0)
      = ((2*t-1 : ℕ) : ℝ) * r := by
    rw [hb0, additive_valuation]
    have hsum : ∀ g ∈ H, uniform_bivalued_obstruction_cost t r 1 g = r := by
      intro g hg
      rw [uniform_bivalued_obstruction_no_equal_marginal_exact_mms_cost_one_apply]
      have : (g:ℕ) < 2*t-1 := by simpa [hH] using hg
      simp [this]
    rw [Finset.sum_congr rfl hsum, Finset.sum_const, hHcard, nsmul_eq_mul]
  have hc1 : additive_valuation (uniform_bivalued_obstruction_cost t r 1) (bundle_of P 1)
      = ((2*t+1 : ℕ) : ℝ) := by
    rw [hb1, additive_valuation]
    have hsum : ∀ g ∈ Finset.univ.filter (fun g : Fin (4*t) => ¬ (g:ℕ) < 2*t-1),
        uniform_bivalued_obstruction_cost t r 1 g = (1:ℝ) := by
      intro g hg
      rw [uniform_bivalued_obstruction_no_equal_marginal_exact_mms_cost_one_apply]
      have : ¬ (g:ℕ) < 2*t-1 := by simpa using hg
      simp [this]
    rw [Finset.sum_congr rfl hsum, Finset.sum_const,
      uniform_bivalued_obstruction_no_equal_marginal_exact_mms_card_filter_fin_not_lt,
      min_eq_right (by omega)]
    have h4 : 4*t - (2*t-1) = 2*t+1 := by omega
    rw [h4]
    push_cast
    ring
  have hmain : chore_maximin_share 2 (uniform_bivalued_obstruction_cost t r 1)
      ≤ max (((2*t-1 : ℕ) : ℝ) * r) (((2*t+1 : ℕ) : ℝ)) := by
    refine uniform_bivalued_obstruction_no_equal_marginal_exact_mms_mms_le_of_partition _ P _ ?_
    intro k
    have hb : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hb with h | h
    · rw [h, hc0]; exact le_max_left _ _
    · rw [h, hc1]; exact le_max_right _ _
  refine lt_of_le_of_lt hmain ?_
  have e0 : (((2*t-1 : ℕ)) : ℝ) = 2*(t:ℝ) - 1 := by
    push_cast [Nat.cast_sub (show 1 ≤ 2*t by omega)]
    ring
  have e1 : (((2*t+1 : ℕ)) : ℝ) = 2*(t:ℝ) + 1 := by push_cast; ring
  rw [max_lt_iff]
  exact ⟨by rw [e0]; exact harith1, by rw [e1]; exact harith2⟩

/-- For integer t >= 2 and ratio r strictly between 1 + 1/t and 1 + 1/(t-1), the 4t-chore obstruction instance admits no equal-marginal exact-MMS lottery. -/
theorem uniform_bivalued_obstruction_no_equal_marginal_exact_mms
    (t : ℕ) (ht : 2 ≤ t)
    (r : ℝ) (hr_lo : 1 + 1 / (t : ℝ) < r) (hr_hi : r < 1 + 1 / ((t - 1 : ℕ) : ℝ)) :
    ¬ ∃ p ∈ stdSimplex ℝ (Fin (4 * t) → Fin 2),
      is_equal_marginal_lottery p ∧
      is_ex_post_alpha_mms_chores 1 (uniform_bivalued_obstruction_cost t r) p := by
  rintro ⟨p, hp_simplex, hp_eq, hp_mms⟩
  obtain ⟨hp_nonneg, hp_sum⟩ := hp_simplex
  set H : Finset (Fin (4*t)) := Finset.univ.filter (fun g : Fin (4*t) => (g:ℕ) < 2*t-1) with hH
  have htpos : (0:ℝ) < (t:ℝ) := by
    have h : (2:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    linarith
  have hr1 : 1 < r := by
    have h : (0:ℝ) < 1/(t:ℝ) := by positivity
    linarith
  have hrm1 : 0 < r - 1 := by linarith
  have hc0fun : uniform_bivalued_obstruction_cost t r 0 = fun _ : Fin (4*t) => (1:ℝ) := by
    funext g; exact uniform_bivalued_obstruction_no_equal_marginal_exact_mms_cost_zero_apply t r g
  have hmms0 : chore_maximin_share 2 (uniform_bivalued_obstruction_cost t r 0) ≤ 2*(t:ℝ) := by
    rw [hc0fun]
    exact uniform_bivalued_obstruction_no_equal_marginal_exact_mms_mms_const_one_four_mul t ht
  have hmms1 : chore_maximin_share 2 (uniform_bivalued_obstruction_cost t r 1) < (t:ℝ)*(1+r) :=
    uniform_bivalued_obstruction_no_equal_marginal_exact_mms_mms_cost_one_le t ht r hr_lo hr_hi
  have hHcard : H.card = 2*t-1 := by
    rw [hH, Fin.card_filter_val_lt, min_eq_right (by omega)]
  have hkey : ∀ σ : Fin (4*t) → Fin 2, 0 < p σ →
      (((bundle_of σ 1) ∩ H).card : ℝ) ≤ (t:ℝ) - 1 := by
    intro σ hσ
    have hσmms : is_alpha_mms_chores 1 (uniform_bivalued_obstruction_cost t r) σ := hp_mms σ hσ
    have h0 : additive_valuation (uniform_bivalued_obstruction_cost t r 0) (bundle_of σ 0)
        ≤ 2*(t:ℝ) := by
      have h := hσmms 0
      simp only [one_mul] at h
      linarith
    rw [hc0fun, uniform_bivalued_obstruction_no_equal_marginal_exact_mms_additive_valuation_one] at h0
    have hb0 : (bundle_of σ 0).card ≤ 2*t := by
      have hcast : ((bundle_of σ 0).card : ℝ) ≤ ((2*t : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast hcast
    have hb1 : 2*t ≤ (bundle_of σ 1).card := by
      have hsum := uniform_bivalued_obstruction_no_equal_marginal_exact_mms_card_bundle_zero_add_one σ
      omega
    have hb1R : 2*(t:ℝ) ≤ ((bundle_of σ 1).card : ℝ) := by
      have hcast : ((2*t : ℕ) : ℝ) ≤ ((bundle_of σ 1).card : ℝ) := by exact_mod_cast hb1
      push_cast at hcast
      linarith
    have h1 : additive_valuation (uniform_bivalued_obstruction_cost t r 1) (bundle_of σ 1)
        < (t:ℝ)*(1+r) := by
      have h := hσmms 1
      simp only [one_mul] at h
      linarith
    have hdec := uniform_bivalued_obstruction_no_equal_marginal_exact_mms_cost_one_decomp r σ H hH
    rw [hdec] at h1
    have hstep : (r-1) * (((bundle_of σ 1) ∩ H).card : ℝ) < (r-1) * (t:ℝ) := by nlinarith
    have hlt : (((bundle_of σ 1) ∩ H).card : ℝ) < (t:ℝ) :=
      lt_of_mul_lt_mul_left hstep (le_of_lt hrm1)
    have hnatlt : ((bundle_of σ 1) ∩ H).card < t := by exact_mod_cast hlt
    have hnat : ((bundle_of σ 1) ∩ H).card ≤ t - 1 := by omega
    have hcast2 : ((t-1 : ℕ) : ℝ) = (t:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ t)]; norm_num
    calc (((bundle_of σ 1) ∩ H).card : ℝ) ≤ ((t-1 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (t:ℝ) - 1 := hcast2
  have hsum_le : ∑ σ : Fin (4*t) → Fin 2, p σ * (((bundle_of σ 1) ∩ H).card : ℝ)
      ≤ (t:ℝ) - 1 := by
    have hterm : ∀ σ : Fin (4*t) → Fin 2,
        p σ * (((bundle_of σ 1) ∩ H).card : ℝ) ≤ p σ * ((t:ℝ) - 1) := by
      intro σ
      by_cases h : 0 < p σ
      · exact mul_le_mul_of_nonneg_left (hkey σ h) (le_of_lt h)
      · have hpz : p σ = 0 := by
          have hle : p σ ≤ 0 := by linarith [not_lt.mp h, hp_nonneg σ]
          linarith [hp_nonneg σ]
        simp [hpz]
    calc ∑ σ : Fin (4*t) → Fin 2, p σ * (((bundle_of σ 1) ∩ H).card : ℝ)
        ≤ ∑ σ : Fin (4*t) → Fin 2, p σ * ((t:ℝ) - 1) := Finset.sum_le_sum (fun σ _ => hterm σ)
      _ = (∑ σ : Fin (4*t) → Fin 2, p σ) * ((t:ℝ) - 1) := by rw [Finset.sum_mul]
      _ = (t:ℝ) - 1 := by rw [hp_sum]; ring
  have heq : ∑ σ : Fin (4*t) → Fin 2, p σ * (((bundle_of σ 1) ∩ H).card : ℝ)
      = ((2*t-1 : ℕ) : ℝ) / 2 := by
    rw [uniform_bivalued_obstruction_no_equal_marginal_exact_mms_sum_p_mul_card_inter p hp_eq 1 H,
      hHcard]
  have hcontra : ((2*t-1 : ℕ) : ℝ) / 2 ≤ (t:ℝ) - 1 := by
    rw [← heq]; exact hsum_le
  have e0 : (((2*t-1 : ℕ)) : ℝ) = 2*(t:ℝ) - 1 := by
    push_cast [Nat.cast_sub (show 1 ≤ 2*t by omega)]
    ring
  rw [e0] at hcontra
  linarith
