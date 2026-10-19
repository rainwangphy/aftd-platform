import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy
import AFTD.Kb.Tcs.HasMonochromaticFanCopy
import AFTD.Kb.Tcs.MixedRamseyProperty
import AFTD.Kb.Tcs.FanRamseyBound
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopyColourInjective
import AFTD.Kb.Tcs.HasMonochromaticFanCopyColourInjective
import AFTD.Kb.Tcs.MixedDiamondFanRamseyBoundBaseZeroDiamondColours
import AFTD.Kb.Tcs.MixedDiamondFanRamseyBoundLastColourStep
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopyColourInjectiveNonempty
import AFTD.Kb.Tcs.HasMonochromaticFanCopyColourInjectiveNonempty
import AFTD.Kb.Tcs.MixedDiamondFanRamseyBoundSingletonDiamondStep
import AFTD.Kb.Tcs.MixedDiamondFanRamseyBoundAllSingletonsFanColours
import AFTD.Kb.Tcs.MixedDiamondFanRamseyBoundAllSingletonsOneFanColour

/-!
# mixed_diamond_fan_ramsey_bound

Topic: combinatorics   Node: 044fbdbf4e9f

Provenance: helper lemma. step towards diamond_poset_ramsey_number_le

For j ≥ 2, a colouring of the subsets of Fin d with a + b colours contains a monochromatic induced j-diamond in one of the first a colours, or a monochromatic induced F_j in one of the last b colours, provided d ≥ j*a + (j-1)*b + 1 when b > 0 and d ≥ j*a when b = 0.
-/

/-- Theorem 7 of arXiv:2610.20545: with a colours assigned the j-diamond and b colours assigned F_j, the Ramsey number is at most j*a + (j-1)*b + 1 when b > 0, and at most j*a when b = 0. -/
theorem mixed_diamond_fan_ramsey_bound (j a b : ℕ) (hj : 2 ≤ j) (d : ℕ)
    (hd : (if b = 0 then j * a else j * a + (j - 1) * b + 1) ≤ d) :
    mixed_ramsey_property j a b d := by
  classical
  suffices H : ∀ k : ℕ, ∀ a b : ℕ, a + b = k → ∀ d : ℕ,
      (if b = 0 then j * a else j * a + (j - 1) * b + 1) ≤ d →
      mixed_ramsey_property j a b d by
    exact H (a + b) a b rfl d hd
  intro k
  induction k using Nat.strong_induction_on with
  | h k ihk =>
    intro a
    induction a using Nat.strong_induction_on with
    | h a iha =>
      intro b hab d hd'
      rcases Nat.eq_zero_or_pos a with ha0 | ha
      · subst ha0
        rcases Nat.eq_zero_or_pos b with hb0 | hb
        · subst hb0
          intro χ
          exact Fin.elim0 (χ ∅)
        · exact mixed_diamond_fan_ramsey_bound_base_zero_diamond_colours j b d hj hb (by
            have hbne : b ≠ 0 := by omega
            simpa [hbne] using hd')
      · rcases Nat.eq_zero_or_pos b with hb0 | hb
        · subst hb0
          refine mixed_diamond_fan_ramsey_bound_last_colour_step j a d hj ha (by simpa using hd') ?_
          refine iha (a - 1) (by omega) 1 (by omega) d ?_
          have hja : j * a = j * (a - 1) + j := by
            rw [← Nat.mul_succ j (a - 1)]; congr 1; omega
          have hd1 : j * a ≤ d := by simpa using hd'
          simp only [if_neg (show (1:ℕ) ≠ 0 by norm_num)]
          omega
        · have hbne : b ≠ 0 := by omega
          have hdj : j * a + (j - 1) * b + 1 ≤ d := by simpa [hbne] using hd'
          intro χ
          by_cases hA : ∃ (x : Fin d) (c : Fin a), χ {x} = Fin.castAdd b c
          · obtain ⟨x, c, hxc⟩ := hA
            refine mixed_diamond_fan_ramsey_bound_singleton_diamond_step j a b d hj ha hb hdj ?_ χ x c hxc
            refine iha (a - 1) (by omega) (b + 1) (by omega) (d - 1) ?_
            have hja : j * a = j * (a - 1) + j := by
              rw [← Nat.mul_succ j (a - 1)]; congr 1; omega
            have hjb : (j - 1) * (b + 1) = (j - 1) * b + (j - 1) := by rw [Nat.mul_succ]
            simp only [if_neg (show b + 1 ≠ 0 by omega)]
            rw [Nat.le_sub_iff_add_le (by omega : 1 ≤ d)]
            omega
          · push Not at hA
            have hxall : ∀ x : Fin d, ∃ c : Fin b, χ {x} = Fin.natAdd a c := by
              intro x
              rcases Fin.addCases
                  (motive := fun γ => (∃ c : Fin a, γ = Fin.castAdd b c) ∨
                    (∃ c : Fin b, γ = Fin.natAdd a c))
                  (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) (χ {x})
                with ⟨c, hc⟩ | ⟨c, hc⟩
              · exact absurd hc (hA x c)
              · exact ⟨c, hc⟩
            rcases Nat.eq_or_lt_of_le hb with hb1 | hb2
            · have hb1' : b = 1 := by omega
              subst hb1'
              have hjeq : (j - 1) * 1 + 1 = j := by
                rw [Nat.mul_one, Nat.sub_one_add_one (by omega : j ≠ 0)]
              have hdaj : j * a + j ≤ d := by omega
              refine mixed_diamond_fan_ramsey_bound_all_singletons_one_fan_colour j a d hj ha hdaj ?_ χ ?_
              · refine ihk (a + 0) (by omega) a 0 (by omega) (d - j) ?_
                rw [Nat.le_sub_iff_add_le (by omega : j ≤ d)]
                exact hdaj
              · intro x
                obtain ⟨c, hc⟩ := hxall x
                obtain rfl : c = 0 := Subsingleton.elim c 0
                exact hc
            · refine mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours j a b d hj ha hb2 hdj ?_ χ hxall
              refine ihk (a + (b - 1)) (by omega) a (b - 1) (by omega) (d - (j - 1)) ?_
              have hja : j * a = j * (a - 1) + j := by
                rw [← Nat.mul_succ j (a - 1)]; congr 1; omega
              have hjb : (j - 1) * b = (j - 1) * (b - 1) + (j - 1) := by
                rw [← Nat.mul_succ (j - 1) (b - 1)]; congr 1; omega
              have hja2 : j ≤ j * a := Nat.le_mul_of_pos_right j (by omega : 0 < a)
              simp only [if_neg (show b - 1 ≠ 0 by omega)]
              rw [Nat.le_sub_iff_add_le (by omega : j - 1 ≤ d)]
              omega
