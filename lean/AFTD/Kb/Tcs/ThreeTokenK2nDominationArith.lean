import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# three_token_k2n_domination_arith

Topic: graphs   Node: 4fa03935bcf0

Provenance: helper lemma. step towards three_token_k2n_domination_number_le

For every integer n ≥ 4, (n / 2).choose 2 + (n - n / 2).choose 2 + n - 2 ≤ (n + 1)^2 / 4 - 2.
-/

lemma three_token_k2n_domination_arith_choose_two_succ (m : ℕ) :
    (m + 1).choose 2 = m.choose 2 + m := by
  have := Nat.choose_succ_succ m 1
  change (m + 1).choose 2 = m.choose 1 + m.choose 2 at this
  rw [Nat.choose_one_right] at this
  omega

lemma three_token_k2n_domination_arith_choose_two_add_succ (k : ℕ) :
    k.choose 2 + (k + 1).choose 2 = k^2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [three_token_k2n_domination_arith_choose_two_succ (k + 1)]
    have h : (k + 1).choose 2 = k.choose 2 + k :=
      three_token_k2n_domination_arith_choose_two_succ k
    nlinarith

lemma three_token_k2n_domination_arith_even (k : ℕ) :
    (2 * k / 2).choose 2 + (2 * k - 2 * k / 2).choose 2 + 2 * k = (2 * k + 1)^2 / 4 := by
  have h1 : 2 * k / 2 = k := by omega
  have h2 : 2 * k - k = k := by omega
  have h3 : k.choose 2 + k.choose 2 + 2 * k = k^2 + k := by
    have hs := three_token_k2n_domination_arith_choose_two_succ k
    have ha := three_token_k2n_domination_arith_choose_two_add_succ k
    omega
  have h4 : (2 * k + 1)^2 / 4 = k^2 + k := by
    have hr : (2 * k + 1)^2 = 4 * (k^2 + k) + 1 := by ring
    rw [hr]
    omega
  rw [h1, h2, h3, h4]

lemma three_token_k2n_domination_arith_odd (k : ℕ) :
    ((2 * k + 1) / 2).choose 2 + ((2 * k + 1) - (2 * k + 1) / 2).choose 2 + (2 * k + 1) =
      (2 * k + 1 + 1)^2 / 4 := by
  have h1 : (2 * k + 1) / 2 = k := by omega
  have h2 : (2 * k + 1) - k = k + 1 := by omega
  have h3 : k.choose 2 + (k + 1).choose 2 + (2 * k + 1) = (k + 1)^2 := by
    have ha := three_token_k2n_domination_arith_choose_two_add_succ k
    nlinarith
  have h4 : (2 * k + 1 + 1)^2 / 4 = (k + 1)^2 := by
    have hr : (2 * k + 1 + 1)^2 = 4 * (k + 1)^2 := by ring
    rw [hr]
    omega
  rw [h1, h2, h3, h4]

/-- For any natural number n >= 4, the sum (n/2).choose 2 + (n - n/2).choose 2 + n - 2 is at most (n + 1)^2 / 4 - 2 in integer division. -/
theorem three_token_k2n_domination_arith (n : ℕ) (hn : 4 ≤ n) :
    (n / 2).choose 2 + (n - n / 2).choose 2 + n - 2 ≤ (n + 1)^2 / 4 - 2 := by
  have h_eq : (n / 2).choose 2 + (n - n / 2).choose 2 + n = (n + 1)^2 / 4 := by
    rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      exact three_token_k2n_domination_arith_even k
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      exact three_token_k2n_domination_arith_odd k
  rw [h_eq]
