import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine

Topic: elementary_number_theory   Node: ad4b142d1674

Provenance: helper lemma. lemma for postage_stamp_number_neg_two_add_one_eq_iff: the extremal family found by exhaustive search (experiments 3511, 3512), r = 0, 1, 2 checked.

For h = 12r + 9, the set {-(2r+2), 2r+2, 4r+5} (which contains a negative integer) has h-range at least ⌊(h²+6h+1)/4⌋ - 1 = n_h(2) - 1.
-/

lemma postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_cons (k : ℕ) (A : Finset ℤ)
    (n a : ℤ) (hn : int_mem_h_fold_sumset k A n) (ha : a ∈ A) :
    int_mem_h_fold_sumset (k + 1) A (a + n) := by
  obtain ⟨f, hf, hs⟩ := hn
  refine ⟨Fin.cons a f, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using hf j
  · rw [Fin.sum_univ_succ]
    simp [hs]

lemma postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_add (A : Finset ℤ) (s : ℤ)
    (hs : s ∈ A) (k : ℕ) (n : ℤ) (hn : int_mem_h_fold_sumset k A n) :
    ∀ c : ℕ, int_mem_h_fold_sumset (k + c) A (n + c * s) := by
  intro c
  induction c with
  | zero => simpa using hn
  | succ c ih =>
    have := postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_cons (k + c) A _ s ih hs
    have e : s + (n + (c : ℤ) * s) = n + ((c + 1 : ℕ) : ℤ) * s := by push_cast; ring
    rw [e] at this
    rw [show k + (c + 1) = k + c + 1 by omega]
    exact this

lemma postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_counts (A : Finset ℤ)
    (p q s : ℤ) (hp : p ∈ A) (hq : q ∈ A) (hs : s ∈ A) (c1 c2 c3 : ℕ) :
    int_mem_h_fold_sumset (c1 + c2 + c3) A ((c1 : ℤ) * p + (c2 : ℤ) * q + (c3 : ℤ) * s) := by
  have h0 : int_mem_h_fold_sumset 0 A 0 := ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  have h1 := postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_add A p hp 0 0 h0 c1
  have h2 := postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_add A q hq _ _ h1 c2
  have h3 := postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_add A s hs _ _ h2 c3
  simpa using h3

lemma postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_rep (r : ℕ) (q ρ j : ℤ)
    (h0 : 0 ≤ ρ + j * (2 * (r : ℤ) + 2)) (h1 : ρ + j * (2 * (r : ℤ) + 2) ≤ 12 * (r : ℤ) + 9)
    (hD1 : -(12 * (r : ℤ) + 9 - (ρ + j * (2 * (r : ℤ) + 2))) ≤
      q - j - 2 * ρ - 2 * j * (2 * (r : ℤ) + 2))
    (hD2 : q - j - 2 * ρ - 2 * j * (2 * (r : ℤ) + 2) ≤
      12 * (r : ℤ) + 9 - (ρ + j * (2 * (r : ℤ) + 2)))
    (hpar : (12 * (r : ℤ) + 9 - (ρ + j * (2 * (r : ℤ) + 2)) -
      (q - j - 2 * ρ - 2 * j * (2 * (r : ℤ) + 2))) % 2 = 0) :
    int_mem_h_fold_sumset (12 * r + 9) {-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5}
      (q * (2 * (r : ℤ) + 2) + ρ) := by
  set c3 : ℤ := ρ + j * (2 * (r : ℤ) + 2) with hc3
  set D : ℤ := q - j - 2 * ρ - 2 * j * (2 * (r : ℤ) + 2) with hD
  set e : ℤ := (12 * (r : ℤ) + 9 - c3 - D) / 2 with he
  have he2 : 2 * e = 12 * (r : ℤ) + 9 - c3 - D := by omega
  have hc := postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_counts
    {-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5}
    (-(2 * (r : ℤ) + 2)) (2 * (r : ℤ) + 2) (4 * (r : ℤ) + 5) (by simp) (by simp) (by simp)
    e.toNat (e + D).toNat c3.toNat
  have he0 : 0 ≤ e := by omega
  have heD : 0 ≤ e + D := by omega
  rw [Int.toNat_of_nonneg he0, Int.toNat_of_nonneg heD, Int.toNat_of_nonneg h0] at hc
  have hsum : e.toNat + (e + D).toNat + c3.toNat = 12 * r + 9 := by omega
  rw [hsum] at hc
  have hv : q * (2 * (r : ℤ) + 2) + ρ =
      e * -(2 * (r : ℤ) + 2) + (e + D) * (2 * (r : ℤ) + 2) + c3 * (4 * (r : ℤ) + 5) := by
    rw [hD, hc3]; ring
  rw [hv]
  exact hc

theorem postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine (r : ℕ) :
    ((12 * r + 9) ^ 2 + 6 * (12 * r + 9) + 1) / 4 - 1 ≤
      postage_stamp_basis_range (12 * r + 9)
        {-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5} := by
  have hN : ((12 * r + 9) ^ 2 + 6 * (12 * r + 9) + 1) / 4 - 1 = 36 * r ^ 2 + 72 * r + 33 := by
    have e : (12 * r + 9) ^ 2 + 6 * (12 * r + 9) + 1 = 4 * (36 * r ^ 2 + 72 * r + 34) := by ring
    rw [e, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
    omega
  rw [hN]
  have key : ∀ q ρ : ℕ, ρ < 2 * r + 2 → q * (2 * r + 2) + ρ ≤ 36 * r ^ 2 + 72 * r + 33 →
      int_mem_h_fold_sumset (12 * r + 9) {-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5}
        ((q : ℤ) * (2 * (r : ℤ) + 2) + (ρ : ℤ)) := by
    intro q ρ hρ hn
    have hq1 : q ≤ 18 * r + 17 := by nlinarith
    have hq2 : q = 18 * r + 17 → ρ + 1 ≤ 2 * r := by
      intro hq; subst hq; nlinarith
    have hρZ : (ρ : ℤ) < 2 * (r : ℤ) + 2 := by exact_mod_cast hρ
    have hq1Z : (q : ℤ) ≤ 18 * (r : ℤ) + 17 := by exact_mod_cast hq1
    have hq2Z : (q : ℤ) = 18 * (r : ℤ) + 17 → (ρ : ℤ) + 1 ≤ 2 * (r : ℤ) := by
      intro h; exact_mod_cast hq2 (by exact_mod_cast h)
    have hq0 : (0 : ℤ) ≤ q := Nat.cast_nonneg q
    have hρ0 : (0 : ℤ) ≤ ρ := Nat.cast_nonneg ρ
    have hr0 : (0 : ℤ) ≤ r := Nat.cast_nonneg r
    have hcases : ∀ j : ℤ, (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) → True := fun _ _ => trivial
    clear hcases
    rcases (show
      ((q : ℤ) ≤ 12 * r + 9 + ρ ∧ ((q : ℤ) - ρ) % 2 = 1) ∨
      ((q : ℤ) ≤ 14 * r + 12 + ρ ∧ 3 * (ρ : ℤ) - 6 * r - 2 ≤ q ∧ ((q : ℤ) - ρ) % 2 = 0) ∨
      ((q : ℤ) ≤ 16 * r + 15 + ρ ∧ 3 * (ρ : ℤ) + 5 ≤ q ∧ ((q : ℤ) - ρ) % 2 = 1) ∨
      ((q : ℤ) ≤ 18 * r + 18 + ρ ∧ 3 * (ρ : ℤ) + 6 * r + 12 ≤ q ∧ ((q : ℤ) - ρ) % 2 = 0) ∨
      ((q : ℤ) ≤ 20 * r + 21 + ρ ∧ 3 * (ρ : ℤ) + 12 * r + 19 ≤ q ∧ ((q : ℤ) - ρ) % 2 = 1)
      by omega) with h | h | h | h | h
    · exact postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_rep r q ρ 0
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_rep r q ρ 1
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_rep r q ρ 2
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_rep r q ρ 3
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine_rep r q ρ 4
        (by omega) (by omega) (by omega) (by omega) (by omega)
  have hmem : ∀ n : ℕ, n ≤ 36 * r ^ 2 + 72 * r + 33 →
      int_mem_h_fold_sumset (12 * r + 9) {-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5}
        (n : ℤ) := by
    intro n hn
    have hdm := Nat.div_add_mod n (2 * r + 2)
    have hρ := Nat.mod_lt n (show 0 < 2 * r + 2 by omega)
    have := key (n / (2 * r + 2)) (n % (2 * r + 2)) hρ (by rw [mul_comm]; omega)
    have e : (n : ℤ) = ((n / (2 * r + 2) : ℕ) : ℤ) * (2 * (r : ℤ) + 2) + ((n % (2 * r + 2) : ℕ) : ℤ) := by
      have : (n : ℤ) = (((2 * r + 2) * (n / (2 * r + 2)) + n % (2 * r + 2) : ℕ) : ℤ) := by
        rw [hdm]
      rw [this]; push_cast; ring
    rw [e]; exact this
  have hbdd : BddAbove {n : ℕ | ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset (12 * r + 9)
      {-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5} m} := by
    refine ⟨(12 * r + 9) * (4 * r + 5), fun n hn => ?_⟩
    obtain ⟨f, hf, hs⟩ := hn n le_rfl
    have hle : ∀ i, f i ≤ 4 * (r : ℤ) + 5 := by
      intro i
      have := hf i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      have : (0 : ℤ) ≤ r := Nat.cast_nonneg r
      omega
    have : (n : ℤ) ≤ ((12 * r + 9 : ℕ) : ℤ) * (4 * (r : ℤ) + 5) := by
      rw [← hs]
      calc ∑ i, f i ≤ ∑ _i : Fin (12 * r + 9), (4 * (r : ℤ) + 5) := Finset.sum_le_sum (fun i _ => hle i)
        _ = _ := by simp
    have : (n : ℤ) ≤ (((12 * r + 9) * (4 * r + 5) : ℕ) : ℤ) := by push_cast at this ⊢; linarith
    exact_mod_cast this
  exact le_csSup hbdd hmem
