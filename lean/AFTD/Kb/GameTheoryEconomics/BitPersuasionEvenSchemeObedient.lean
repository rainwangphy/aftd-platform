import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenCoord
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenPrior
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenScheme
import AFTD.Kb.GameTheoryEconomics.IsObedientDirectScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrSchemeObedient
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenState
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenCoupling

/-!
# bit_persuasion_even_scheme_obedient

Topic: mechanism_design   Node: 8f273bee7cf1

Provenance: helper lemma. arXiv:2606.22226

For every natural number m ≥ 1, bit_persuasion_even_scheme m is an obedient direct scheme for bit_persuasion_even_prior m (is_obedient_direct_scheme (bit_persuasion_even_prior m) (bit_persuasion_even_scheme m)).
-/

open Finset

lemma bit_persuasion_even_scheme_obedient_card_ne (m : ℕ) (s : Fin (2 * m)) :
    (univ.filter (fun t : Fin (2 * m) => s ≠ t)).card = 2 * m - 1 := by
  have : (univ.filter (fun t : Fin (2 * m) => s ≠ t)) = univ.erase s := by
    ext t
    simp [ne_comm]
  rw [this, card_erase_of_mem (mem_univ s), card_univ, Fintype.card_fin]

lemma bit_persuasion_even_scheme_obedient_coupling_nonneg (m : ℕ) (hm : 1 ≤ m)
    (x y : bit_persuasion_even_coord m → Bool) :
    0 ≤ bit_persuasion_even_coupling m x y := by
  unfold bit_persuasion_even_coupling
  apply sum_nonneg; intro s _
  apply sum_nonneg; intro t _
  split_ifs
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hpos1 : (0 : ℝ) < 2 * m := by linarith
    have hpos2 : (0 : ℝ) < 2 * m - 1 := by linarith
    positivity
  · rfl

lemma bit_persuasion_even_scheme_obedient_coupling_symm (m : ℕ)
    (x y : bit_persuasion_even_coord m → Bool) :
    bit_persuasion_even_coupling m x y = bit_persuasion_even_coupling m y x := by
  unfold bit_persuasion_even_coupling
  rw [sum_comm]
  apply sum_congr rfl; intro s _
  apply sum_congr rfl; intro t _
  by_cases h : t ≠ s ∧ bit_persuasion_even_state m t = x ∧ bit_persuasion_even_state m s = y
  · have h' : s ≠ t ∧ bit_persuasion_even_state m s = y ∧ bit_persuasion_even_state m t = x :=
      ⟨h.1.symm, h.2.2, h.2.1⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬(s ≠ t ∧ bit_persuasion_even_state m s = y ∧ bit_persuasion_even_state m t = x) := by
      rintro ⟨h1, h2, h3⟩
      exact h ⟨h1.symm, h3, h2⟩
    rw [if_neg h, if_neg h']

lemma bit_persuasion_even_scheme_obedient_coupling_marginal (m : ℕ) (hm : 1 ≤ m)
    (x : bit_persuasion_even_coord m → Bool) :
    ∑ y, bit_persuasion_even_coupling m x y = bit_persuasion_even_prior m x := by
  classical
  unfold bit_persuasion_even_coupling bit_persuasion_even_prior
  rw [sum_comm]
  apply sum_congr rfl; intro s _
  rw [sum_comm]
  by_cases hs : bit_persuasion_even_state m s = x
  · rw [if_pos hs]
    have e : ∀ t, (∑ y, if s ≠ t ∧ bit_persuasion_even_state m s = x ∧
        bit_persuasion_even_state m t = y then 1 / ((2 * m : ℝ) * (2 * m - 1)) else 0) =
        if s ≠ t then 1 / ((2 * m : ℝ) * (2 * m - 1)) else 0 := by
      intro t
      by_cases ht : s ≠ t
      · simp only [ht, hs, true_and, if_true, ne_eq, not_false_eq_true]
        rw [sum_ite_eq]
        simp
      · simp [ht]
    rw [sum_congr rfl (fun t _ => e t), ← sum_filter, Finset.sum_const,
      bit_persuasion_even_scheme_obedient_card_ne, nsmul_eq_mul]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have h1 : (2 * (m : ℝ) - 1 : ℝ) ≠ 0 := by linarith
    have h2 : (2 * (m : ℝ) : ℝ) ≠ 0 := by linarith
    have hle : 1 ≤ 2 * m := by omega
    push_cast [hle]
    field_simp
  · rw [if_neg hs]
    apply sum_eq_zero; intro t _
    apply sum_eq_zero; intro y _
    simp [hs]

open Finset in
/-- For m ≥ 1, the pair-OR signaling scheme for the two-layer construction is obedient. -/
theorem bit_persuasion_even_scheme_obedient (m : ℕ) (hm : 1 ≤ m) :
    is_obedient_direct_scheme (bit_persuasion_even_prior m) (bit_persuasion_even_scheme m) := by
  exact persuasion_pair_or_scheme_obedient _ _
    (bit_persuasion_even_scheme_obedient_coupling_nonneg m hm)
    (bit_persuasion_even_scheme_obedient_coupling_symm m)
    (bit_persuasion_even_scheme_obedient_coupling_marginal m hm)
