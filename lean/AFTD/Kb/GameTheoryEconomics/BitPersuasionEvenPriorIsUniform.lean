import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsUniformBitPrior
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenPrior
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenPriorIsBitPrior
import AFTD.Kb.GameTheoryEconomics.IsBitPrior
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenCoord
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenState

/-!
# bit_persuasion_even_prior_is_uniform

Topic: mechanism_design   Node: 641479e66531

Provenance: helper lemma. OP-1547; arXiv:2606.22226

For every natural number m with 1 ≤ m, the function bit_persuasion_even_prior m is a uniform bit prior on 2 * m states (is_uniform_bit_prior (2 * m) (bit_persuasion_even_prior m)).
-/

open Finset in
lemma bit_persuasion_even_prior_is_uniform_state_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (bit_persuasion_even_state m) := by
  intro s1 s2 h
  by_contra hne
  have h_univ : (univ \ {s1, s2} : Finset (Fin (2 * m))).card = 2 * m - 2 := by
    rw [card_sdiff_of_subset (subset_univ _)]
    rw [card_univ, Fintype.card_fin, card_pair hne]
  have h_le : m - 1 ≤ (univ \ {s1, s2} : Finset (Fin (2 * m))).card := by
    rw [h_univ]
    omega
  obtain ⟨t, ht_sub, ht_card⟩ := exists_subset_card_eq h_le
  have hs1_notin_t : s1 ∉ t := by
    intro hs1
    have := ht_sub hs1
    rw [mem_sdiff, mem_insert, mem_singleton] at this
    exact this.2 (Or.inl rfl)
  have hs2_notin_t : s2 ∉ t := by
    intro hs2
    have := ht_sub hs2
    rw [mem_sdiff, mem_insert, mem_singleton] at this
    exact this.2 (Or.inr rfl)
  let B : Finset (Fin (2 * m)) := insert s1 t
  have hB_card : B.card = m := by
    dsimp [B]
    rw [card_insert_of_notMem hs1_notin_t, ht_card]
    omega
  have hs1_in_B : s1 ∈ B := mem_insert_self s1 t
  have hs2_notin_B : s2 ∉ B := by
    rw [mem_insert, not_or]
    exact ⟨Ne.symm hne, hs2_notin_t⟩
  have hj : 0 < 3 * m := by omega
  let c : bit_persuasion_even_coord m := Sum.inr (⟨B, hB_card⟩, ⟨0, hj⟩)
  have h1 : bit_persuasion_even_state m s1 c = true := by
    dsimp [bit_persuasion_even_state, c]
    simp [hs1_in_B]
  have h2 : bit_persuasion_even_state m s2 c = false := by
    dsimp [bit_persuasion_even_state, c]
    simp [hs2_notin_B]
  have hc : bit_persuasion_even_state m s1 c = bit_persuasion_even_state m s2 c := by
    rw [h]
  rw [h1, h2] at hc
  cases hc

open Finset in
lemma bit_persuasion_even_prior_is_uniform_prior_eq_of_mem (m : ℕ) (hm : 1 ≤ m) (s : Fin (2 * m)) :
    bit_persuasion_even_prior m (bit_persuasion_even_state m s) = 1 / (2 * (m : ℝ)) := by
  unfold bit_persuasion_even_prior
  have hinj := bit_persuasion_even_prior_is_uniform_state_injective m hm
  have h_eq : ∀ s', (bit_persuasion_even_state m s' = bit_persuasion_even_state m s) ↔ s' = s := by
    intro s'
    exact hinj.eq_iff
  simp_rw [h_eq]
  rw [sum_ite_eq']
  simp

open Finset in
lemma bit_persuasion_even_prior_is_uniform_prior_eq_zero_of_not_mem (m : ℕ)
    (x : bit_persuasion_even_coord m → Bool)
    (hx : ∀ s, bit_persuasion_even_state m s ≠ x) :
    bit_persuasion_even_prior m x = 0 := by
  unfold bit_persuasion_even_prior
  have : ∀ s ∈ (univ : Finset (Fin (2 * m))), (if bit_persuasion_even_state m s = x then 1 / (2 * (m : ℝ)) else 0) = 0 := by
    intro s _
    rw [if_neg (hx s)]
  rw [sum_congr rfl this, sum_const_zero]

open Finset in
/-- The two-layer prior on 2m states is a uniform bit prior on 2m states. -/
theorem bit_persuasion_even_prior_is_uniform (m : ℕ) (hm : 1 ≤ m) :
    is_uniform_bit_prior (2 * m) (bit_persuasion_even_prior m) := by
  unfold is_uniform_bit_prior
  refine ⟨bit_persuasion_even_prior_is_bit_prior m hm, ?_, ?_⟩
  · have h_supp : (univ.filter (fun x => bit_persuasion_even_prior m x ≠ 0)) =
        univ.image (bit_persuasion_even_state m) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro hne
        by_contra h_not
        apply hne
        apply bit_persuasion_even_prior_is_uniform_prior_eq_zero_of_not_mem
        intro s hs
        exact h_not ⟨s, hs⟩
      · rintro ⟨s, _, rfl⟩
        rw [bit_persuasion_even_prior_is_uniform_prior_eq_of_mem m hm s]
        have hm0 : (m : ℝ) ≠ 0 := by positivity
        positivity
    rw [h_supp]
    rw [card_image_of_injective _ (bit_persuasion_even_prior_is_uniform_state_injective m hm)]
    rw [card_univ, Fintype.card_fin]
  · intro x hx
    have h_ex : ∃ s, bit_persuasion_even_state m s = x := by
      by_contra h_not
      apply hx
      apply bit_persuasion_even_prior_is_uniform_prior_eq_zero_of_not_mem
      intro s hs
      exact h_not ⟨s, hs⟩
    obtain ⟨s, rfl⟩ := h_ex
    rw [bit_persuasion_even_prior_is_uniform_prior_eq_of_mem m hm s]
    push_cast
    rfl
