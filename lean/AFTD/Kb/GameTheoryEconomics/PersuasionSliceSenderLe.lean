import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceState
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord
import AFTD.Kb.GameTheoryEconomics.IsObedientDirectScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePrior
import AFTD.Kb.GameTheoryEconomics.PersuasionSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionObedienceCost
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCardFilter
import AFTD.Kb.GameTheoryEconomics.PersuasionHeavySetsCardLe
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePriorIsBitPrior

/-!
# persuasion_slice_sender_le

Topic: mechanism_design   Node: b9258d8eba70

Sender value of the slice prior. No obedient scheme gives the sender more than C(2m+1,m) - C(2m-1,m).
-/

open Finset in
/-- For `m ≥ 1` the `2m+1` states of the slice prior are distinct. -/
lemma persuasion_slice_state_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (persuasion_slice_state m) := by
  intro s t h
  by_contra hst
  obtain ⟨i, hsi, hit, hic⟩ := exists_subsuperset_card_eq
    (show ({s} : Finset (Fin (2 * m + 1))) ⊆ Finset.univ.erase t by
      intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact mem_erase.mpr ⟨hst, Finset.mem_univ _⟩)
    (show ({s} : Finset (Fin (2 * m + 1))).card ≤ m by simpa using hm)
    (show m ≤ (Finset.univ.erase t).card by
      rw [card_erase_of_mem (Finset.mem_univ t), card_univ, Fintype.card_fin]; omega)
  have := congrFun h ⟨i, hic⟩
  simp only [persuasion_slice_state] at this
  have h1 : s ∈ i := hsi (Finset.mem_singleton_self s)
  have h2 : t ∉ i := fun ht => by simpa using hit ht
  simp [h1, h2] at this

open Finset in
/-- **Sender value of the slice prior.** No obedient scheme gives the sender more than
`C(2m+1,m) - C(2m-1,m)`. -/
lemma persuasion_slice_sender_le (m : ℕ) (hm : 1 ≤ m)
    (q : (persuasion_slice_coord m → Bool) → (persuasion_slice_coord m → Bool) → ℝ)
    (hq : is_obedient_direct_scheme (persuasion_slice_prior m) q) :
    persuasion_sender_utility q ≤ ((2 * m + 1).choose m : ℝ) - (2 * m - 1).choose m := by
  classical
  set B : ℝ := ((2 * m + 1).choose m : ℝ) - (2 * m - 1).choose m
  set v := persuasion_slice_state m
  have hinj := persuasion_slice_state_injective m hm
  obtain ⟨hq0, hqμ, hqob⟩ := hq
  -- `q` vanishes off the support
  have hsupp : ∀ x a, (∀ s, v s ≠ x) → q x a = 0 := by
    intro x a hx
    have hμ0 : persuasion_slice_prior m x = 0 := by
      unfold persuasion_slice_prior
      apply sum_eq_zero; intro s _; rw [if_neg (hx s)]
    apply le_antisymm _ (hq0 x a)
    rw [← hμ0, ← hqμ x]
    exact single_le_sum (fun a' _ => hq0 x a') (Finset.mem_univ a)
  have hsum : ∀ a (g : (persuasion_slice_coord m → Bool) → ℝ),
      ∑ x, q x a * g x = ∑ s, q (v s) a * g (v s) := by
    intro a g
    rw [← sum_image (s := (Finset.univ : Finset (Fin (2 * m + 1)))) (g := v)
      (f := fun x => q x a * g x) (fun s _ t _ h => hinj h)]
    symm
    apply sum_subset (Finset.subset_univ _)
    intro x _ hx
    rw [hsupp x a (fun s hs => hx (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, hs⟩)), zero_mul]
  -- per action
  have hact : ∀ a, ∑ x, q x a * ((Finset.univ.filter (fun i => a i = true)).card : ℝ) ≤
      ∑ x, q x a * B := by
    intro a
    rw [← sum_mul, ← sum_mul]
    have hQ : 0 ≤ ∑ x, q x a := sum_nonneg fun x _ => hq0 x a
    rcases hQ.lt_or_eq with hQ | hQ
    swap
    · rw [← hQ, zero_mul, zero_mul]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    set w : Fin (2 * m + 1) → ℝ := fun s => q (v s) a
    have hw0 : ∀ s, 0 ≤ w s := fun s => hq0 _ a
    have hW : ∑ s, w s = ∑ x, q x a := by
      have := hsum a (fun _ => 1); simp only [mul_one] at this; rw [this]
    have hWpos : 0 < ∑ s, w s := hW ▸ hQ
    -- every recommended coordinate is heavy
    have hheavy : ∀ i : persuasion_slice_coord m, a i = true →
        ∑ s, w s ≤ 2 * ∑ s ∈ i.1, w s := by
      intro i hai
      have h := hqob a i
      rw [hsum a (fun x => persuasion_obedience_cost i x a)] at h
      unfold persuasion_obedience_cost at h
      simp only [hai, if_true] at h
      have e : ∀ s, q (v s) a * (1 / 2 - if v s i = true then 1 else 0) =
          w s / 2 - if s ∈ i.1 then w s else 0 := by
        intro s
        simp only [w, v, persuasion_slice_state, decide_eq_true_eq]
        split_ifs <;> ring
      rw [sum_congr rfl (fun s _ => e s), sum_sub_distrib, sum_ite_mem, Finset.univ_inter,
        ← sum_div] at h
      linarith
    have hcard : (Finset.univ.filter (fun i : persuasion_slice_coord m => a i = true)).card ≤
        ((powersetCard m (Finset.univ : Finset (Fin (2 * m + 1)))).filter
          (fun j => ∑ s, w s ≤ 2 * ∑ s ∈ j, w s)).card := by
      rw [← persuasion_slice_card_filter m (fun j => ∑ s, w s ≤ 2 * ∑ s ∈ j, w s)]
      exact Finset.card_le_card (fun i hi => by
        rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hheavy i hi.2⟩)
    have hmain := persuasion_heavy_sets_card_le m hm w hw0 hWpos
    have : (Finset.univ.filter (fun i : persuasion_slice_coord m => a i = true)).card +
        (2 * m - 1).choose m ≤ (2 * m + 1).choose m := by omega
    simp only [B]
    have : ((Finset.univ.filter (fun i : persuasion_slice_coord m => a i = true)).card : ℝ) +
        (2 * m - 1).choose m ≤ (2 * m + 1).choose m := by exact_mod_cast this
    linarith
  unfold persuasion_sender_utility
  rw [sum_comm]
  calc ∑ a, ∑ x, q x a * ((Finset.univ.filter (fun i => a i = true)).card : ℝ)
      ≤ ∑ a, ∑ x, q x a * B := sum_le_sum fun a _ => hact a
    _ = ∑ x, persuasion_slice_prior m x * B := by
        rw [sum_comm]; apply sum_congr rfl; intro x _; rw [← sum_mul, hqμ x]
    _ = B := by rw [← sum_mul, (persuasion_slice_prior_is_bit_prior m).2, one_mul]
