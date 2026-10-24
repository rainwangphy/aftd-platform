import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.PostageStampNumberNeg
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddUpperFour
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_number_neg_two_add_four_le_of_mod_sixty_eq

Topic: elementary_number_theory   Node: 64ff763d1997

Provenance: original. Related work: arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 (n♭_h(2) < n_h(2) for odd h)

For odd h ≥ 5 with h ≡ 59 (mod 60), n♭_h(2) ≤ n_h(2) - 4, where n_h(2) = ⌊(h²+6h+1)/4⌋.
-/

theorem postage_stamp_number_neg_two_add_four_le_of_mod_sixty_eq (h : ℕ) (hh : 5 ≤ h)
    (ho : h % 2 = 1) (h59 : h % 60 = 59) :
    postage_stamp_number_neg h 2 + 4 ≤ (h ^ 2 + 6 * h + 1) / 4 := by
  have hne : {n | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧
      postage_stamp_basis_range h A = n}.Nonempty :=
    ⟨_, {-1, 0, 1}, by rfl, ⟨-1, by simp, by norm_num⟩, rfl⟩
  have h25 : 25 ≤ h ^ 2 := by nlinarith
  have := csSup_le hne (fun n hn => show n ≤ (h ^ 2 + 6 * h + 1) / 4 - 4 by
    obtain ⟨A, hA, hneg, rfl⟩ := hn
    have := postage_stamp_number_neg_two_of_odd_upper_four h hh ho h59 A hA hneg
    omega)
  unfold postage_stamp_number_neg
  omega
