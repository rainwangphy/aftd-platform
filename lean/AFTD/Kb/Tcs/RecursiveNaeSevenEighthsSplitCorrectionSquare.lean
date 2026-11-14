import AFTD.Prelude

/-!
# recursive_nae_seven_eighths_split_correction_square

Topic: quantum   Node: a4c3d40c214c

Provenance: helper lemma. Integer form of the balanced correction estimate for arXiv:2611.16412, Section 5.2; experiment 27234.

For every natural depth d, with k the rounded-up seven-eighths split, two to the power d plus twice k is at most three to the power twice k. This is the squared integer form of the split correction estimate.
-/

private def in868_split (d : ℕ) := (7*d+7)/8

private theorem in868_split_add_eight (d : ℕ) : in868_split (d+8) = in868_split d+7 := by
  dsimp [in868_split]
  omega

theorem recursive_nae_seven_eighths_split_correction_square (d : ℕ) : 2^(d + 2*((7*d+7)/8)) ≤ 3^(2*((7*d+7)/8)) := by
  change 2^(d + 2*in868_split d) ≤ 3^(2*in868_split d)
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases h : d < 8
    · interval_cases d <;> norm_num [in868_split]
    · have hd : d-8+8=d := by omega
      have hs : in868_split d = in868_split (d-8)+7 := by
        have hh := in868_split_add_eight (d-8)
        rw [hd] at hh
        exact hh
      have he : d+2*in868_split d = ((d-8)+2*in868_split (d-8))+22 := by omega
      have hf : 2*in868_split d = 2*in868_split (d-8)+14 := by omega
      calc
        _ = 2^((d-8)+2*in868_split (d-8))*2^22 := by rw [he, pow_add]
        _ ≤ 3^(2*in868_split (d-8))*3^14 := Nat.mul_le_mul (ih (d-8) (by omega)) (by norm_num)
        _ = _ := by rw [hf, pow_add]
