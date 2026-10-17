import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.PostageStampNumber
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetLeOfForallLe
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetOfList
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_number_three_eight_eq

Topic: elementary_number_theory   Node: a97b02636f05

Provenance: formalization of a published result. Source: Classical value of the postage stamp problem with three positive denominations (OEIS A001212, h = 8); recomputed exhaustively in experiment 726. Used by arXiv:2610.19470 (Positivity and negativity for h-bases for n) only for k = 2.

The classical postage stamp number with four stamps (one of them 0) and h = 8: n_8(3) = 89, attained by {0, 1, 9, 14}.
-/

/-- Bitmask of `h{0, 1, a, b} ⊆ ℕ`: bit `m` is set when `m` is a sum of `h` elements. -/
def postage_stamp_number_three_eight_eq_bits (a b : ℕ) : ℕ → ℕ
  | 0 => 1
  | h + 1 => postage_stamp_number_three_eight_eq_step a b (postage_stamp_number_three_eight_eq_bits a b h)
where postage_stamp_number_three_eight_eq_step (a b s : ℕ) : ℕ := s ||| (s <<< 1) ||| (s <<< a) ||| (s <<< b)

theorem postage_stamp_number_three_eight_eq_bits_sound (a b : ℕ) (A : Finset ℤ) (hA : A = {0, 1, (a : ℤ), (b : ℤ)}) (h : ℕ)
    (m : ℤ) (hm : int_mem_h_fold_sumset h A m) (hm98 : m ≤ 98) :
    0 ≤ m ∧ (postage_stamp_number_three_eight_eq_bits (min a 99) (min b 99) h).testBit m.toNat = true := by
  induction h generalizing m with
  | zero =>
    obtain ⟨f, -, rfl⟩ := hm
    simp [postage_stamp_number_three_eight_eq_bits]
  | succ h ih =>
    obtain ⟨f, hf, rfl⟩ := hm
    have hnn : ∀ i, 0 ≤ f i := by
      intro i; have := hf i; rw [hA] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h | h <;> omega
    rw [Fin.sum_univ_succ] at hm98 ⊢
    have htn : 0 ≤ ∑ i : Fin h, f i.succ := Finset.sum_nonneg (fun i _ => hnn _)
    have h00 := hnn 0
    obtain ⟨-, ht⟩ := ih (∑ i : Fin h, f i.succ) ⟨fun i => f i.succ, fun i => hf _, rfl⟩
      (by omega)
    refine ⟨by omega, ?_⟩
    have h0 := hf 0
    rw [hA] at h0
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0
    simp only [postage_stamp_number_three_eight_eq_bits, postage_stamp_number_three_eight_eq_bits.postage_stamp_number_three_eight_eq_step, Nat.testBit_lor, Nat.testBit_shiftLeft]
    generalize ∑ i : Fin h, f i.succ = t at ht htn hm98 ⊢
    rcases h0 with h0 | h0 | h0 | h0 <;> rw [h0] at hm98 ⊢
    · simp [ht]
    · rw [show (1 + t).toNat = t.toNat + 1 by omega]; simp [ht]
    · rw [show ((a : ℤ) + t).toNat = t.toNat + min a 99 by omega]; simp [ht]
    · rw [show ((b : ℤ) + t).toNat = t.toNat + min b 99 by omega]; simp [ht]

theorem postage_stamp_number_three_eight_eq_check : ∀ a < 100, ∀ b < 100, 2 ≤ a → 2 ≤ b →
    ∃ m < 91, (postage_stamp_number_three_eight_eq_bits a b 8).testBit m = false := by
  decide +kernel

theorem postage_stamp_number_three_eight_eq_basis_range_ge : 89 ≤ postage_stamp_basis_range 8 {0, 1, 9, 14} := by
  have key : ∀ m : ℕ, m ≤ 89 → ∃ i j k : Fin 9, i.val + j.val + k.val ≤ 8 ∧
      (m : ℤ) = 0 * (8 - i.val - j.val - k.val : ℕ) + i.val + 9 * j.val + 14 * k.val := by
    decide +kernel
  apply le_csSup
  · refine ⟨112, fun n hn => ?_⟩
    have := int_mem_h_fold_sumset_le_of_forall_le 8 _ 14 (by decide) _ (hn n le_rfl)
    omega
  · intro m hm
    obtain ⟨i, j, k, hijk, he⟩ := key m hm
    have := int_mem_h_fold_sumset_of_list {0, 1, 9, 14}
      (List.replicate (8 - i.val - j.val - k.val) 0 ++ List.replicate i.val 1 ++
        List.replicate j.val 9 ++ List.replicate k.val 14) (by
          intro x hx
          simp only [List.mem_append, List.mem_replicate] at hx
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega)
    have hlen : (List.replicate (8 - i.val - j.val - k.val) 0 ++ List.replicate i.val 1 ++
        List.replicate j.val 9 ++ List.replicate k.val (14 : ℤ)).length = 8 := by
      simp only [List.length_append, List.length_replicate]; omega
    rw [hlen] at this
    convert this using 1
    simp only [List.sum_append, List.sum_replicate]
    rw [he]; ring

theorem postage_stamp_number_three_eight_eq : postage_stamp_number 8 3 = 89 := by
  have key : ∀ A : Finset ℤ, A.card = 3 + 1 → (∀ a ∈ A, 0 ≤ a) →
      ∃ m0 : ℕ, m0 ≤ 90 ∧ ¬ int_mem_h_fold_sumset 8 A m0 := by
    intro A hcard hnn
    by_cases h0 : (0 : ℤ) ∈ A
    · by_cases h1 : (1 : ℤ) ∈ A
      · have hB : ((A.erase 0).erase 1).card = 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨by norm_num, h1⟩),
            Finset.card_erase_of_mem h0, hcard]
        obtain ⟨x, y, hxy, hBxy⟩ := Finset.card_eq_two.1 hB
        have hx : x ∈ (A.erase 0).erase 1 := by rw [hBxy]; simp
        have hy : y ∈ (A.erase 0).erase 1 := by rw [hBxy]; simp
        simp only [Finset.mem_erase] at hx hy
        have hx0 := hnn x hx.2.2
        have hy0 := hnn y hy.2.2
        have hA : A = {0, 1, ((x.toNat : ℕ) : ℤ), ((y.toNat : ℕ) : ℤ)} := by
          ext z
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0]
          constructor
          · intro hz
            by_cases hz0 : z = 0
            · exact Or.inl hz0
            by_cases hz1 : z = 1
            · exact Or.inr (Or.inl hz1)
            have : z ∈ (A.erase 0).erase 1 := by simp [hz, hz0, hz1]
            rw [hBxy] at this
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            tauto
          · rintro (rfl | rfl | rfl | rfl)
            · exact h0
            · exact h1
            · exact hx.2.2
            · exact hy.2.2
        obtain ⟨m, hm, hbit⟩ := postage_stamp_number_three_eight_eq_check (min x.toNat 99) (by omega) (min y.toNat 99) (by omega)
          (by omega) (by omega)
        refine ⟨m, by omega, fun hmem => ?_⟩
        have := (postage_stamp_number_three_eight_eq_bits_sound x.toNat y.toNat A hA 8 m hmem (by omega)).2
        simp only [Int.toNat_natCast] at this
        rw [this] at hbit
        exact Bool.noConfusion hbit
      · refine ⟨1, by norm_num, fun ⟨f, hf, hs⟩ => h1 ?_⟩
        have hfn : ∀ i, 0 ≤ f i := fun i => hnn _ (hf i)
        obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
          by_contra hne
          simp only [not_exists, not_not] at hne
          simp [hne] at hs
        have hle : f i ≤ ∑ j, f j :=
          Finset.single_le_sum (fun j _ => hfn j) (Finset.mem_univ i)
        have : f i = 1 := by have := hfn i; push_cast at hs; omega
        exact this ▸ hf i
    · refine ⟨0, by norm_num, fun ⟨f, hf, hs⟩ => h0 ?_⟩
      have hfn : ∀ i, 0 ≤ f i := fun i => hnn _ (hf i)
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hfn i)).1 (by exact_mod_cast hs) 0
        (Finset.mem_univ _)
      exact this ▸ hf 0
  have hle : ∀ n ∈ {n | ∃ A : Finset ℤ, A.card = 3 + 1 ∧ (∀ a ∈ A, 0 ≤ a) ∧
      postage_stamp_basis_range 8 A = n}, n ≤ 89 := by
    rintro n ⟨A, hcard, hnn, rfl⟩
    obtain ⟨m0, hm0, hnot⟩ := key A hcard hnn
    apply csSup_le'
    intro n hn
    by_contra hlt
    exact hnot (hn m0 (by omega))
  have hge := postage_stamp_number_three_eight_eq_basis_range_ge
  refine le_antisymm (csSup_le' hle) (hge.trans (le_csSup ⟨89, hle⟩ ⟨{0, 1, 9, 14}, by decide,
    by decide, rfl⟩))
