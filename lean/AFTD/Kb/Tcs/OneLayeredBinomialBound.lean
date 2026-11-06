import AFTD.Prelude
import AFTD.Kb.Tcs.OneLayeredMaxLayers
import AFTD.Kb.Tcs.OneLayeredRecurrence
import AFTD.Kb.Tcs.OneLayeredMaxLayersOfLt
import AFTD.Kb.Tcs.OneLayeredFamily

/-!
# one_layered_binomial_bound

Topic: combinatorics   Node: e4bbad60efb7

Provenance: formalization of a published result. Source: arXiv:2611.08071 Theorem 2.1

For all integers r ≥ 1 and m ≥ r, the maximum number of layers F(m, r) in a 1-layered family of r-subsets on at most m vertices satisfies F(m, r) ≤ (m - r + 1) * Nat.choose (Nat.log 2 (m - r + 1) + r - 1) (r - 1).
-/

private def one_layered_binomial_bound_B (m r : ℕ) : ℕ :=
  (m - r + 1) * Nat.choose (Nat.log 2 (m - r + 1) + r - 1) (r - 1)

private lemma one_layered_binomial_bound_sSup_le {m r B : ℕ}
    (h : ∀ n ≤ m, ∀ F : OneLayeredFamily (Fin n) r, F.k ≤ B) :
    one_layered_max_layers m r ≤ B := by
  unfold one_layered_max_layers
  refine csSup_le' ?_
  rintro k ⟨n, hn, F, rfl⟩
  exact h n hn F

private lemma one_layered_binomial_bound_k_le_of_one {n : ℕ} (F : OneLayeredFamily (Fin n) 1) :
    F.k ≤ n := by
  classical
  choose u hu using F.layers_nonempty
  have hcard : ∀ t, (u t).card = 1 := fun t => F.layers_card t (u t) (hu t)
  choose v hv using fun t => Finset.card_eq_one.mp (hcard t)
  have hinj : Function.Injective v := by
    intro s t hst
    by_contra hne
    have h₁ : u s ∈ F.layers s := hu s
    have h₂ : u s ∈ F.layers t := by
      have hst' : u s = u t := by rw [hv s, hv t, hst]
      rw [hst']
      exact hu t
    exact Finset.disjoint_left.mp (F.layers_disjoint s t hne) h₁ h₂
  simpa using Fintype.card_le_of_injective v hinj

/-- The binomial upper bound F(m, r) ≤ (m - r + 1) * choose(⌊log_2(m - r + 1)⌋ + r - 1, r - 1). -/
theorem one_layered_binomial_bound (m r : ℕ) (hr : 1 ≤ r) (hm : r ≤ m) :
    one_layered_max_layers m r ≤ (m - r + 1) * Nat.choose (Nat.log 2 (m - r + 1) + r - 1) (r - 1) := by
  have main : ∀ m r, 1 ≤ r → r ≤ m → one_layered_max_layers m r ≤ one_layered_binomial_bound_B m r := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih r hr hm
    rcases eq_or_lt_of_le hr with hr1 | hr2
    · subst hr1
      have hbase : one_layered_max_layers m 1 ≤ m := by
        refine one_layered_binomial_bound_sSup_le ?_
        intro n hn F
        exact (one_layered_binomial_bound_k_le_of_one F).trans hn
      simpa [one_layered_binomial_bound_B, Nat.sub_add_cancel (by omega : 1 ≤ m)] using hbase
    · have hrec := one_layered_recurrence m r hr2 hm
      refine hrec.trans ?_
      have h1 : one_layered_max_layers ((m - 1) / 2) r ≤
          (if r ≤ (m - 1) / 2 then ((m - 1) / 2 - r + 1) else 0) *
            Nat.choose (Nat.log 2 (m - r + 1) + r - 2) (r - 1) := by
        by_cases hra : r ≤ (m - 1) / 2
        · rw [if_pos hra]
          have hih := ih ((m - 1) / 2) (by omega) r (by omega) hra
          refine hih.trans ?_
          unfold one_layered_binomial_bound_B
          apply Nat.mul_le_mul_left
          apply Nat.choose_le_choose
          have hlog : Nat.log 2 ((m - 1) / 2 - r + 1) + 1 ≤ Nat.log 2 (m - r + 1) := by
            have h2 : 2 * ((m-1)/2 - r + 1) ≤ m - r + 1 := by omega
            have hpos : (m-1)/2 - r + 1 ≠ 0 := by omega
            have hpow : 2 ^ (Nat.log 2 ((m-1)/2 - r + 1) + 1) ≤ m - r + 1 := by
              rw [Nat.pow_succ]
              calc 2 ^ Nat.log 2 ((m-1)/2 - r + 1) * 2 ≤ ((m-1)/2 - r + 1) * 2 := by
                    gcongr
                    exact Nat.pow_log_le_self 2 hpos
                _ ≤ m - r + 1 := by omega
            exact Nat.le_log_of_pow_le (by norm_num) hpow
          omega
        · rw [if_neg hra]
          rw [one_layered_max_layers_of_lt _ _ (by omega)]
          simp
      have h2 : one_layered_max_layers (m / 2) r ≤
          (if r ≤ m / 2 then (m / 2 - r + 1) else 0) *
            Nat.choose (Nat.log 2 (m - r + 1) + r - 2) (r - 1) := by
        by_cases hrb : r ≤ m / 2
        · rw [if_pos hrb]
          have hih := ih (m / 2) (by omega) r (by omega) hrb
          refine hih.trans ?_
          unfold one_layered_binomial_bound_B
          apply Nat.mul_le_mul_left
          apply Nat.choose_le_choose
          have hlog : Nat.log 2 (m / 2 - r + 1) + 1 ≤ Nat.log 2 (m - r + 1) := by
            have h2 : 2 * (m/2 - r + 1) ≤ m - r + 1 := by omega
            have hpos : m/2 - r + 1 ≠ 0 := by omega
            have hpow : 2 ^ (Nat.log 2 (m/2 - r + 1) + 1) ≤ m - r + 1 := by
              rw [Nat.pow_succ]
              calc 2 ^ Nat.log 2 (m/2 - r + 1) * 2 ≤ (m/2 - r + 1) * 2 := by
                    gcongr
                    exact Nat.pow_log_le_self 2 hpos
                _ ≤ m - r + 1 := by omega
            exact Nat.le_log_of_pow_le (by norm_num) hpow
          omega
        · rw [if_neg hrb]
          rw [one_layered_max_layers_of_lt _ _ (by omega)]
          simp
      have h3 : one_layered_max_layers (m - 1) (r - 1) ≤
          (m - r + 1) * Nat.choose (Nat.log 2 (m - r + 1) + r - 2) (r - 2) := by
        have hih := ih (m - 1) (by omega) (r - 1) (by omega) (by omega)
        refine hih.trans ?_
        unfold one_layered_binomial_bound_B
        have e1 : (m - 1) - (r - 1) + 1 = m - r + 1 := by omega
        have e2 : (r - 1) - 1 = r - 2 := by omega
        rw [e1, e2]
        have e3 : Nat.log 2 (m - r + 1) + (r - 1) - 1 = Nat.log 2 (m - r + 1) + r - 2 := by omega
        rw [e3]
      refine (add_le_add (add_le_add h1 h2) h3).trans ?_
      unfold one_layered_binomial_bound_B
      set A' := (if r ≤ (m - 1) / 2 then ((m - 1) / 2 - r + 1) else 0) with hA'
      set B' := (if r ≤ m / 2 then (m / 2 - r + 1) else 0) with hB'
      set C1 := Nat.choose (Nat.log 2 (m - r + 1) + r - 2) (r - 1) with hC1
      set C2 := Nat.choose (Nat.log 2 (m - r + 1) + r - 2) (r - 2) with hC2
      have hsum : A' + B' ≤ m - r + 1 := by
        rw [hA', hB']
        by_cases h1' : r ≤ (m-1)/2
        · have h2' : r ≤ m / 2 := by omega
          rw [if_pos h1', if_pos h2']
          omega
        · rw [if_neg h1']
          by_cases h2' : r ≤ m / 2
          · rw [if_pos h2']
            have hle : m / 2 - r + 1 ≤ m - r + 1 := by
              apply Nat.add_le_add_right
              exact Nat.sub_le_sub_right (by omega) r
            omega
          · rw [if_neg h2']; omega
      have hC : Nat.choose (Nat.log 2 (m - r + 1) + r - 1) (r - 1) = C1 + C2 := by
        have hp := Nat.choose_succ_succ' (Nat.log 2 (m - r + 1) + r - 2) (r - 2)
        have e1 : Nat.log 2 (m - r + 1) + r - 2 + 1 = Nat.log 2 (m - r + 1) + r - 1 := by omega
        have e2 : r - 2 + 1 = r - 1 := by omega
        rw [e1, e2] at hp
        rw [hC1, hC2]
        exact hp.trans (Nat.add_comm _ _)
      calc A' * C1 + B' * C1 + (m - r + 1) * C2
          = (A' + B') * C1 + (m - r + 1) * C2 := by ring
        _ ≤ (m - r + 1) * C1 + (m - r + 1) * C2 := by
              gcongr
        _ = (m - r + 1) * (C1 + C2) := by ring
        _ = (m - r + 1) * Nat.choose (Nat.log 2 (m - r + 1) + r - 1) (r - 1) := by rw [hC]
  exact main m r hr hm
