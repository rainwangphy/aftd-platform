import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WomanCutoffTanking
import AFTD.Kb.GameTheoryEconomics.ManCutoffTanking
import AFTD.Kb.GameTheoryEconomics.WomanCutoffTankingGeSubset
import AFTD.Kb.GameTheoryEconomics.WomanCutoffTankingIsStableOfGe
import AFTD.Kb.GameTheoryEconomics.IsBlockingPair
import AFTD.Kb.GameTheoryEconomics.MoveToBottom
import AFTD.Kb.GameTheoryEconomics.MarriageMarket
import AFTD.Kb.GameTheoryEconomics.IsStableMatching

/-!
# exact_cutoff_filtering

Topic: matching_markets   Node: b386191a8f10

Provenance: formalization of a published result. Source: arXiv:2610.42105 Theorem 4.3

In a finite marriage market with strict complete preference profile Q, for every agent (woman w with stable partner t in M, or man m with stable partner t in W), the set of stable matchings of the profile obtained by t-cutoff tanking by that agent equals the set of stable matchings in S(Q) that assign that agent a partner ranked weakly above t.
-/

open Classical

lemma exact_cutoff_filtering_pref_m_tanked_irrefl {M W : Type*} (market : MarriageMarket M W)
    (h_m_strict : ∀ m, IsStrictTotalOrder W (market.pref_m m))
    (w : W) (t : M) (m : M) (x : W) :
    ¬ (woman_cutoff_tanking market w t).pref_m m x x := by
  dsimp [woman_cutoff_tanking]
  split_ifs
  · dsimp [move_to_bottom]
    split_ifs with h1
    · trivial
    · exact (h_m_strict m).irrefl x
  · exact (h_m_strict m).irrefl x

lemma exact_cutoff_filtering_pref_m_tanked_of_market {M W : Type*} (market : MarriageMarket M W)
    (h_w_strict : ∀ w, IsStrictTotalOrder M (market.pref_w w))
    (w : W) (t : M) (μ ν : M ≃ W) (h_nu_t : ν t = w)
    (m' : M) (h : market.pref_m m' (ν m') (μ m')) :
    (woman_cutoff_tanking market w t).pref_m m' (ν m') (μ m') := by
  dsimp [woman_cutoff_tanking]
  split_ifs with hwt
  · dsimp [move_to_bottom]
    have h_m'_ne_t : m' ≠ t := by
      intro heq
      have := (h_w_strict w).irrefl t
      rw [heq] at hwt
      exact this hwt
    have h_nu_ne_w : ν m' ≠ w := by
      intro heq
      have : ν m' = ν t := by rw [heq, h_nu_t]
      exact h_m'_ne_t (ν.injective this)
    rw [if_neg h_nu_ne_w]
    by_cases hmu : μ m' = w
    · rw [if_pos hmu]
      trivial
    · rw [if_neg hmu]
      exact h
  · exact h

lemma exact_cutoff_filtering_step_w {M W : Type*} (market : MarriageMarket M W)
    (h_m_strict : ∀ m, IsStrictTotalOrder W (market.pref_m m))
    (h_w_strict : ∀ w, IsStrictTotalOrder M (market.pref_w w))
    (w : W) (t : M) (μ ν : M ≃ W)
    (h_mu_stable : is_stable_matching (woman_cutoff_tanking market w t) μ)
    (m : M)
    (h_m_step : (woman_cutoff_tanking market w t).pref_m m (ν m) (μ m)) :
    market.pref_w (ν m) (μ.symm (ν m)) m := by
  have h_not_bp := h_mu_stable m (ν m)
  dsimp [is_blocking_pair] at h_not_bp
  have h_not_w : ¬ (woman_cutoff_tanking market w t).pref_w (ν m) m (μ.symm (ν m)) := by
    intro hw
    exact h_not_bp ⟨h_m_step, hw⟩
  dsimp [woman_cutoff_tanking] at h_not_w
  have := h_w_strict (ν m)
  rcases trichotomous_of (market.pref_w (ν m)) (μ.symm (ν m)) m with h1 | h2 | h3
  · exact h1
  · exfalso
    have : ν m = μ m := by
      have h_eq : μ (μ.symm (ν m)) = μ m := by rw [h2]
      rw [μ.apply_symm_apply] at h_eq
      exact h_eq
    rw [this] at h_m_step
    exact exact_cutoff_filtering_pref_m_tanked_irrefl market h_m_strict w t m (μ m) h_m_step
  · exfalso
    exact h_not_w h3

lemma exact_cutoff_filtering_step_m {M W : Type*} (market : MarriageMarket M W)
    (h_m_strict : ∀ m, IsStrictTotalOrder W (market.pref_m m))
    (h_w_strict : ∀ w, IsStrictTotalOrder M (market.pref_w w))
    (μ ν : M ≃ W)
    (h_nu_stable : is_stable_matching market ν)
    (m : M)
    (hw : market.pref_w (ν m) (μ.symm (ν m)) m) :
    market.pref_m (μ.symm (ν m)) (ν (μ.symm (ν m))) (μ (μ.symm (ν m))) := by
  let m' := μ.symm (ν m)
  have h_not_bp := h_nu_stable m' (ν m)
  dsimp [is_blocking_pair] at h_not_bp
  have h_not_m : ¬ market.pref_m m' (ν m) (ν m') := by
    intro hm
    have hw_sub : market.pref_w (ν m) m' (ν.symm (ν m)) := by
      rw [ν.symm_apply_apply]
      exact hw
    exact h_not_bp ⟨hm, hw_sub⟩
  have := h_m_strict m'
  have h_w_eq : ν m = μ m' := by
    dsimp [m']
    rw [μ.apply_symm_apply]
  rcases trichotomous_of (market.pref_m m') (ν m') (μ m') with h1 | h2 | h3
  · exact h1
  · exfalso
    have h_eq : ν m' = ν m := by rw [h2, h_w_eq]
    have h_m'_eq : m' = m := ν.injective h_eq
    have hw' : market.pref_w (ν m) m' m := hw
    rw [h_m'_eq] at hw'
    exact (h_w_strict (ν m)).irrefl m hw'
  · exfalso
    rw [← h_w_eq] at h3
    exact h_not_m h3

lemma exact_cutoff_filtering_base_step {M W : Type*} (market : MarriageMarket M W)
    (h_w_strict : ∀ w, IsStrictTotalOrder M (market.pref_w w))
    (w : W) (t : M) (μ ν : M ≃ W) (h_nu_t : ν t = w)
    (h_w_pref : market.pref_w w t (μ.symm w)) :
    (woman_cutoff_tanking market w t).pref_m (μ.symm w) (ν (μ.symm w)) (μ (μ.symm w)) := by
  dsimp [woman_cutoff_tanking]
  rw [if_pos h_w_pref]
  dsimp [move_to_bottom]
  have h_ne_t : μ.symm w ≠ t := by
    intro heq
    have := (h_w_strict w).irrefl t
    rw [heq] at h_w_pref
    exact this h_w_pref
  have h_nu_ne_w : ν (μ.symm w) ≠ w := by
    intro heq
    have : ν (μ.symm w) = ν t := by rw [heq, h_nu_t]
    exact h_ne_t (ν.injective this)
  rw [if_neg h_nu_ne_w]
  rw [if_pos (μ.apply_symm_apply w)]
  trivial

lemma exact_cutoff_filtering_woman_ge_of_stable {M W : Type*} [Fintype M] [Fintype W]
    (market : MarriageMarket M W)
    (h_m_strict : ∀ m, IsStrictTotalOrder W (market.pref_m m))
    (h_w_strict : ∀ w, IsStrictTotalOrder M (market.pref_w w))
    (w : W) (t : M) (ν : M ≃ W)
    (h_nu_stable : is_stable_matching market ν)
    (h_nu_t : ν.symm w = t)
    (μ : M ≃ W)
    (h_mu_stable : is_stable_matching (woman_cutoff_tanking market w t) μ) :
    ¬ market.pref_w w t (μ.symm w) := by
  intro h_w_pref
  have h_nu_t_apply : ν t = w := by
    rw [← h_nu_t, ν.apply_symm_apply]
  let f : Equiv.Perm M := ν.trans μ.symm
  have h_f_t : f t = μ.symm w := by
    dsimp [f]
    rw [h_nu_t_apply]
  let m₀ := μ.symm w
  have h_base : (woman_cutoff_tanking market w t).pref_m m₀ (ν m₀) (μ m₀) :=
    exact_cutoff_filtering_base_step market h_w_strict w t μ ν h_nu_t_apply h_w_pref
  have h_ind_m : ∀ n : ℕ, (woman_cutoff_tanking market w t).pref_m ((f ^ n) m₀) (ν ((f ^ n) m₀)) (μ ((f ^ n) m₀)) := by
    intro n
    induction' n with n ih
    · exact h_base
    · rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]
      have hw := exact_cutoff_filtering_step_w market h_m_strict h_w_strict w t μ ν h_mu_stable ((f ^ n) m₀) ih
      have hm := exact_cutoff_filtering_step_m market h_m_strict h_w_strict μ ν h_nu_stable ((f ^ n) m₀) hw
      change (woman_cutoff_tanking market w t).pref_m (f ((f ^ n) m₀)) (ν (f ((f ^ n) m₀))) (μ (f ((f ^ n) m₀)))
      exact exact_cutoff_filtering_pref_m_tanked_of_market market h_w_strict w t μ ν h_nu_t_apply (f ((f ^ n) m₀)) hm
  let k := orderOf f
  have hk : 0 < k := orderOf_pos f
  let N := k - 1
  have h_eq_t : (f ^ N) m₀ = t := by
    have h1 : (f ^ k) m₀ = m₀ := by rw [pow_orderOf_eq_one]; rfl
    have h2 : k = N + 1 := (Nat.sub_add_cancel hk).symm
    rw [h2, pow_succ', Equiv.Perm.coe_mul, Function.comp_apply] at h1
    apply f.injective
    rw [h_f_t]
    exact h1
  have hw_N := exact_cutoff_filtering_step_w market h_m_strict h_w_strict w t μ ν h_mu_stable ((f ^ N) m₀) (h_ind_m N)
  rw [h_eq_t, h_nu_t_apply] at hw_N
  have := (h_w_strict w).irrefl t (_root_.trans h_w_pref hw_N)
  exact this

def exact_cutoff_filtering_swap_market {M W : Type*} (market : MarriageMarket M W) : MarriageMarket W M :=
  ⟨market.pref_w, market.pref_m⟩

lemma exact_cutoff_filtering_is_stable_matching_swap {M W : Type*} (market : MarriageMarket M W) (μ : M ≃ W) :
    is_stable_matching (exact_cutoff_filtering_swap_market market) μ.symm ↔ is_stable_matching market μ := by
  dsimp [is_stable_matching, is_blocking_pair, exact_cutoff_filtering_swap_market]
  constructor <;> intro h a b <;> have := h b a <;> tauto

lemma exact_cutoff_filtering_man_cutoff_tanking_swap {M W : Type*} (market : MarriageMarket M W) (m : M) (t : W) :
    exact_cutoff_filtering_swap_market (man_cutoff_tanking market m t) = woman_cutoff_tanking (exact_cutoff_filtering_swap_market market) m t := by
  rfl

/-- Theorem 4.3 (Exact cutoff filtering): the set of stable matchings after t-cutoff tanking by an agent equals the stable matchings of the original profile assigning that agent a partner weakly preferred to t. -/
theorem exact_cutoff_filtering {M W : Type*} [Fintype M] [Fintype W]
    (market : MarriageMarket M W)
    (h_m_strict : ∀ m, IsStrictTotalOrder W (market.pref_m m))
    (h_w_strict : ∀ w, IsStrictTotalOrder M (market.pref_w w)) :
    (∀ (w : W) (t : M) (_ : ∃ μ : M ≃ W, is_stable_matching market μ ∧ μ.symm w = t),
      {μ : M ≃ W | is_stable_matching (woman_cutoff_tanking market w t) μ} =
      {μ : M ≃ W | is_stable_matching market μ ∧ ¬ market.pref_w w t (μ.symm w)}) ∧
    (∀ (m : M) (t : W) (_ : ∃ μ : M ≃ W, is_stable_matching market μ ∧ μ m = t),
      {μ : M ≃ W | is_stable_matching (man_cutoff_tanking market m t) μ} =
      {μ : M ≃ W | is_stable_matching market μ ∧ ¬ market.pref_m m t (μ m)}) := by
  constructor
  · intro w t ⟨ν, h_nu_stable, h_nu_t⟩
    ext μ
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h_tank_stable
      have h_ge := exact_cutoff_filtering_woman_ge_of_stable market h_m_strict h_w_strict w t ν h_nu_stable h_nu_t μ h_tank_stable
      have hw_trans : ∀ a b c : M, market.pref_w w a b → market.pref_w w b c → market.pref_w w a c :=
        fun a b c hab hbc => _root_.trans hab hbc
      exact ⟨woman_cutoff_tanking_is_stable_of_ge market w t hw_trans μ h_tank_stable h_ge, h_ge⟩
    · rintro ⟨h_stable, h_ge⟩
      exact woman_cutoff_tanking_ge_subset market w t μ h_stable h_ge
  · intro m t ⟨ν, h_nu_stable, h_nu_t⟩
    ext μ
    simp only [Set.mem_setOf_eq]
    have h_w_strict_swap : ∀ (w : W), IsStrictTotalOrder M ((exact_cutoff_filtering_swap_market market).pref_m w) := h_w_strict
    have h_m_strict_swap : ∀ (m : M), IsStrictTotalOrder W ((exact_cutoff_filtering_swap_market market).pref_w m) := h_m_strict
    have h_nu_symm_m : ν.symm.symm m = t := h_nu_t
    have h_nu_swap_stable : is_stable_matching (exact_cutoff_filtering_swap_market market) ν.symm := by
      rw [exact_cutoff_filtering_is_stable_matching_swap]
      exact h_nu_stable
    constructor
    · intro h_tank_stable
      have h_tank_swap_stable : is_stable_matching (woman_cutoff_tanking (exact_cutoff_filtering_swap_market market) m t) μ.symm := by
        rw [← exact_cutoff_filtering_man_cutoff_tanking_swap]
        rw [exact_cutoff_filtering_is_stable_matching_swap]
        exact h_tank_stable
      have h_ge := exact_cutoff_filtering_woman_ge_of_stable (exact_cutoff_filtering_swap_market market) h_w_strict_swap h_m_strict_swap m t ν.symm h_nu_swap_stable h_nu_symm_m μ.symm h_tank_swap_stable
      dsimp [exact_cutoff_filtering_swap_market] at h_ge
      have hm_trans : ∀ a b c : W, market.pref_m m a b → market.pref_m m b c → market.pref_m m a c :=
        fun a b c hab hbc => _root_.trans hab hbc
      have h_orig_swap : is_stable_matching (exact_cutoff_filtering_swap_market market) μ.symm :=
        woman_cutoff_tanking_is_stable_of_ge (exact_cutoff_filtering_swap_market market) m t hm_trans μ.symm h_tank_swap_stable h_ge
      rw [exact_cutoff_filtering_is_stable_matching_swap] at h_orig_swap
      exact ⟨h_orig_swap, h_ge⟩
    · rintro ⟨h_stable, h_ge⟩
      have h_swap_stable : is_stable_matching (exact_cutoff_filtering_swap_market market) μ.symm := by
        rw [exact_cutoff_filtering_is_stable_matching_swap]
        exact h_stable
      have h_tank_swap : is_stable_matching (woman_cutoff_tanking (exact_cutoff_filtering_swap_market market) m t) μ.symm :=
        woman_cutoff_tanking_ge_subset (exact_cutoff_filtering_swap_market market) m t μ.symm h_swap_stable h_ge
      rw [← exact_cutoff_filtering_man_cutoff_tanking_swap] at h_tank_swap
      rw [exact_cutoff_filtering_is_stable_matching_swap] at h_tank_swap
      exact h_tank_swap
