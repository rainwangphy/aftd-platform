import AFTD.Prelude
import AFTD.Kb.Tcs.MonotoneMixtureWeight
import AFTD.Kb.Tcs.UniformDistribution
import AFTD.Kb.Tcs.MonotoneMixtureWeightNonneg
import AFTD.Kb.Tcs.MonotoneMixtureWeightSumByParts
import AFTD.Kb.Tcs.MonotoneDistributionTelescopingSum
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# mixture_representation_monotone_distribution

Topic: information   Node: 66ca7f7eca90

Provenance: formalization of a published result. Source: arXiv:2610.01563 Lemma 3

Let $P : \mathbb{N}^+ \to \mathbb{R}$ be a nonincreasing probability distribution on the positive integers, so that $P(k) \ge 0$ for all $k$, $P$ is antitone, and $\sum_{k=1}^\infty P(k) = 1$. Then the mixture weights $w_k = k(P(k) - P(k+1))$ satisfy: $w_k \ge 0$ for all $k \in \mathbb{N}^+$; $\sum_{k=1}^\infty w_k = 1$; for every $n \in \mathbb{N}^+$, $\sum_{k=n}^\infty \frac{w_k}{k} = P(n)$; and for every $n \in \mathbb{N}^+$, $\sum_{k=1}^\infty w_k U_k(n) = P(n)$, where $U_k$ is the uniform distribution on $\{1, \dots, k\}$.
-/

open Filter
open scoped Topology

private lemma mixture_representation_monotone_distribution_succPNat_add_one (m : ℕ) :
    Nat.succPNat m + 1 = Nat.succPNat (m + 1) := by
  apply PNat.coe_injective
  show ((Nat.succPNat m : ℕ+) : ℕ) + 1 = ((Nat.succPNat (m + 1) : ℕ+) : ℕ)
  simp [Nat.succPNat]

private lemma mixture_representation_monotone_distribution_succPNat_val (m : ℕ) :
    ((Nat.succPNat m : ℕ+) : ℕ) = m + 1 := by
  simp [Nat.succPNat]

private lemma mixture_representation_monotone_distribution_succPNat_val_real (m : ℕ) :
    ((Nat.succPNat m : ℕ+) : ℝ) = (m : ℝ) + 1 := by
  have h := mixture_representation_monotone_distribution_succPNat_val m
  push_cast [h]
  ring

private lemma mixture_representation_monotone_distribution_succPNat_natPred (n : ℕ+) :
    Nat.succPNat ((n : ℕ) - 1) = n := by
  apply PNat.coe_injective
  show ((Nat.succPNat ((n : ℕ) - 1) : ℕ+) : ℕ) = (n : ℕ)
  rw [mixture_representation_monotone_distribution_succPNat_val]
  have := n.pos
  omega

private lemma mixture_representation_monotone_distribution_pnat_hassum_iff {a : ℕ+ → ℝ} {s : ℝ} :
    HasSum a s ↔ HasSum (fun m : ℕ => a (Nat.succPNat m)) s := by
  have h := Equiv.hasSum_iff (Equiv.pnatEquivNat.symm) (f := a) (a := s)
  have he : (a ∘ ⇑(Equiv.pnatEquivNat.symm)) = fun m : ℕ => a (Nat.succPNat m) := by
    funext m; simp
  rw [he] at h
  exact h.symm

private lemma mixture_representation_monotone_distribution_monotone_succPNat :
    Monotone (Nat.succPNat : ℕ → ℕ+) := by
  intro a b hab
  refine (PNat.coe_le_coe _ _).mp ?_
  rw [mixture_representation_monotone_distribution_succPNat_val,
    mixture_representation_monotone_distribution_succPNat_val]
  omega

private lemma mixture_representation_monotone_distribution_succPNat_le_iff (n : ℕ+) (m : ℕ) :
    n ≤ Nat.succPNat m ↔ (n : ℕ) - 1 ≤ m := by
  rw [← PNat.coe_le_coe, mixture_representation_monotone_distribution_succPNat_val]
  have := n.pos
  omega

private lemma mixture_representation_monotone_distribution_tail_tendsto (Q : ℕ → ℝ)
    (hsum : Summable Q) :
    Tendsto (fun N : ℕ => ∑' i : ℕ, Q (i + N)) atTop (𝓝 0) := by
  have heq : (fun N : ℕ => ∑' i : ℕ, Q (i + N))
      = fun N => (∑' i : ℕ, Q i) - ∑ i ∈ Finset.range N, Q i := by
    funext N
    have h := hsum.sum_add_tsum_nat_add N
    linarith
  rw [heq]
  have hc : Tendsto (fun _ : ℕ => (∑' i : ℕ, Q i)) atTop (𝓝 (∑' i : ℕ, Q i)) :=
    tendsto_const_nhds
  simpa using hc.sub hsum.tendsto_sum_tsum_nat

private lemma mixture_representation_monotone_distribution_block_le_tail (Q : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ Q n) (hanti : Antitone Q) (hsum : Summable Q) (n : ℕ) :
    (n : ℝ) * Q n ≤ 2 * (∑' i : ℕ, Q (i + n / 2)) := by
  set M := n / 2 with hM
  have hshift : Summable (fun i : ℕ => Q (i + M)) := (summable_nat_add_iff M).mpr hsum
  have step1 : (n : ℝ) * Q n ≤ 2 * (((n + 1 - M : ℕ)) : ℝ) * Q n := by
    have hnum : (n : ℝ) ≤ 2 * ((n + 1 - M : ℕ) : ℝ) := by
      have h : n ≤ 2 * (n + 1 - M) := by omega
      exact_mod_cast h
    have hQn : 0 ≤ Q n := hnonneg n
    nlinarith
  have step2 : (((n + 1 - M : ℕ)) : ℝ) * Q n ≤ ∑ j ∈ Finset.Icc M n, Q j := by
    have h1 : ∑ j ∈ Finset.Icc M n, Q n ≤ ∑ j ∈ Finset.Icc M n, Q j := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_Icc] at hj
      exact hanti hj.2
    have h2 : ∑ j ∈ Finset.Icc M n, Q n = ((Finset.Icc M n).card : ℝ) * Q n := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.Icc M n).card = n + 1 - M := by simp
    rw [h2, hcard] at h1
    exact h1
  have step3 : ∑ j ∈ Finset.Icc M n, Q j ≤ ∑' i : ℕ, Q (i + M) := by
    rw [show Finset.Icc M n = Finset.Ico M (n + 1) from by ext x; simp]
    rw [Finset.sum_Ico_eq_sum_range]
    have : ∑ k ∈ Finset.range (n + 1 - M), Q (M + k)
        = ∑ k ∈ Finset.range (n + 1 - M), Q (k + M) := by
      apply Finset.sum_congr rfl
      intro k _; rw [Nat.add_comm]
    rw [this]
    exact hshift.sum_le_tsum _ (fun i _ => hnonneg _)
  calc (n : ℝ) * Q n ≤ 2 * (((n + 1 - M : ℕ)) : ℝ) * Q n := step1
    _ ≤ 2 * (∑ j ∈ Finset.Icc M n, Q j) := by linarith
    _ ≤ 2 * (∑' i : ℕ, Q (i + M)) := by linarith

private lemma mixture_representation_monotone_distribution_tendsto_nat_mul (Q : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ Q n) (hanti : Antitone Q) (hsum : Summable Q) :
    Tendsto (fun n : ℕ => (n : ℝ) * Q n) atTop (𝓝 0) := by
  have htail := mixture_representation_monotone_distribution_tail_tendsto Q hsum
  have hcomp : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hupper : Tendsto (fun n : ℕ => 2 * (∑' i : ℕ, Q (i + n / 2))) atTop (𝓝 0) := by
    simpa using (htail.comp hcomp).const_mul 2
  apply squeeze_zero' _ _ hupper
  · filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg n) (hnonneg n)
  · filter_upwards with n using
      mixture_representation_monotone_distribution_block_le_tail Q hnonneg hanti hsum n

private lemma mixture_representation_monotone_distribution_weight_sum_identity (Q : ℕ → ℝ) :
    ∀ N : ℕ, ∑ m ∈ Finset.range N, ((m : ℝ) + 1) * (Q m - Q (m + 1))
      = ∑ m ∈ Finset.range N, Q m - (N : ℝ) * Q N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma mixture_representation_monotone_distribution_indicator_sum_identity (Q : ℕ → ℝ)
    {ñ N : ℕ} (h : ñ ≤ N) :
    ∑ m ∈ Finset.range N, (if ñ ≤ m then (Q m - Q (m + 1)) else 0) = Q ñ - Q N := by
  rw [← Finset.sum_filter]
  have hf : (Finset.range N).filter (fun m => ñ ≤ m) = Finset.Ico ñ N := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf]
  have h2 : ∑ m ∈ Finset.Ico ñ N, (Q m - Q (m + 1))
      = -(∑ m ∈ Finset.Ico ñ N, (Q (m + 1) - Q m)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  rw [h2, Finset.sum_Ico_sub Q h]
  ring

/-- Mixture representation of monotone probability distributions on ℕ+ by uniform distributions. -/
theorem mixture_representation_monotone_distribution
    (P : ℕ+ → ℝ) (h_nonneg : ∀ k : ℕ+, 0 ≤ P k) (h_anti : Antitone P) (h_sum : HasSum P 1) :
    (∀ k : ℕ+, 0 ≤ monotoneMixtureWeight P k) ∧
    HasSum (monotoneMixtureWeight P) 1 ∧
    (∀ n : ℕ+, HasSum (fun k : ℕ+ => if n ≤ k then monotoneMixtureWeight P k / (k : ℝ) else 0) (P n)) ∧
    (∀ n : ℕ+, HasSum (fun k : ℕ+ => monotoneMixtureWeight P k * uniformDistribution k n) (P n)) := by
  set Q : ℕ → ℝ := fun m => P (Nat.succPNat m) with hQdef
  have hQnonneg : ∀ m, 0 ≤ Q m := fun m => h_nonneg _
  have hQanti : Antitone Q := fun a b hab =>
    h_anti (mixture_representation_monotone_distribution_monotone_succPNat hab)
  have hQhasSum : HasSum Q 1 :=
    mixture_representation_monotone_distribution_pnat_hassum_iff.mp h_sum
  have hQsum : Summable Q := hQhasSum.summable
  have hw : ∀ m : ℕ, monotoneMixtureWeight P (Nat.succPNat m)
      = ((m : ℝ) + 1) * (Q m - Q (m + 1)) := by
    intro m
    simp only [monotoneMixtureWeight, hQdef]
    rw [mixture_representation_monotone_distribution_succPNat_val_real,
      mixture_representation_monotone_distribution_succPNat_add_one]
  have h2 : HasSum (monotoneMixtureWeight P) 1 := by
    refine mixture_representation_monotone_distribution_pnat_hassum_iff.mpr ?_
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun m => monotoneMixtureWeight_nonneg P h_anti _)]
    have hpartial : ∀ N : ℕ,
        ∑ m ∈ Finset.range N, monotoneMixtureWeight P (Nat.succPNat m)
          = ∑ m ∈ Finset.range N, Q m - (N : ℝ) * Q N := by
      intro N
      rw [← mixture_representation_monotone_distribution_weight_sum_identity Q N]
      exact Finset.sum_congr rfl (fun m _ => hw m)
    rw [show (fun N : ℕ => ∑ m ∈ Finset.range N, monotoneMixtureWeight P (Nat.succPNat m))
        = fun N => ∑ m ∈ Finset.range N, Q m - (N : ℝ) * Q N from funext hpartial]
    have htend : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, Q m - (N : ℝ) * Q N)
        atTop (𝓝 (1 - 0)) :=
      hQhasSum.tendsto_sum_nat.sub
        (mixture_representation_monotone_distribution_tendsto_nat_mul Q hQnonneg hQanti hQsum)
    simpa using htend
  have h3 : ∀ n : ℕ+, HasSum (fun k : ℕ+ => if n ≤ k then monotoneMixtureWeight P k / (k : ℝ) else 0) (P n) := by
    intro n
    refine mixture_representation_monotone_distribution_pnat_hassum_iff.mpr ?_
    set ñ := (n : ℕ) - 1 with hñ
    have hnn : Nat.succPNat ñ = n :=
      mixture_representation_monotone_distribution_succPNat_natPred n
    have hpn : Q ñ = P n := by simp [hQdef, hnn]
    have hle : ∀ m : ℕ, (n ≤ Nat.succPNat m) ↔ (ñ ≤ m) := by
      intro m
      rw [← hnn]
      exact mixture_representation_monotone_distribution_succPNat_le_iff (Nat.succPNat ñ) m
    have hfun : (fun m : ℕ => (if n ≤ Nat.succPNat m then
          monotoneMixtureWeight P (Nat.succPNat m) / ((Nat.succPNat m : ℕ+) : ℝ) else 0))
        = fun m : ℕ => if ñ ≤ m then (Q m - Q (m + 1)) else 0 := by
      funext m
      by_cases h : ñ ≤ m
      · rw [if_pos (hle m |>.mpr h), if_pos h]
        have hpos : ((m : ℝ) + 1) ≠ 0 := by positivity
        rw [hw m, mixture_representation_monotone_distribution_succPNat_val_real,
          mul_div_cancel_left₀ _ hpos]
      · rw [if_neg (fun hc => h ((hle m).mp hc)), if_neg h]
    rw [hfun]
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have hlim : Tendsto (fun N : ℕ => Q ñ - Q N) atTop (𝓝 (Q ñ)) := by
        have h := (tendsto_const_nhds (x := Q ñ) (f := (atTop : Filter ℕ))).sub
          hQsum.tendsto_atTop_zero
        simpa using h
      have hev : (fun N : ℕ => ∑ m ∈ Finset.range N, (if ñ ≤ m then (Q m - Q (m + 1)) else 0))
          =ᶠ[atTop] fun N => Q ñ - Q N := by
        filter_upwards [eventually_ge_atTop ñ] with N hN
        exact mixture_representation_monotone_distribution_indicator_sum_identity Q hN
      have hres := Tendsto.congr' hev.symm hlim
      rw [← hpn]
      exact hres
    · intro m
      by_cases h : ñ ≤ m
      · rw [if_pos h]
        exact sub_nonneg.mpr (hQanti (Nat.le_succ m))
      · rw [if_neg h]
  refine ⟨fun k => monotoneMixtureWeight_nonneg P h_anti k, h2, h3, ?_⟩
  intro n
  have hpt : (fun k : ℕ+ => monotoneMixtureWeight P k * uniformDistribution k n)
      = fun k : ℕ+ => if n ≤ k then monotoneMixtureWeight P k / (k : ℝ) else 0 := by
    funext k
    by_cases h : n ≤ k <;> simp [uniformDistribution, h, div_eq_mul_inv]
  rw [hpt]
  exact h3 n
