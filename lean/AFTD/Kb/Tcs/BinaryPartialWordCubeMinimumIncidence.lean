import AFTD.Prelude
import AFTD.Kb.Tcs.DyadicIntegerTangent
import AFTD.Kb.Tcs.BinaryPartialWordCubeVolumeBound
import AFTD.Kb.Tcs.DyadicIntegerTangentEqIff

/-!
# binary_partial_word_cube_minimum_incidence

Topic: combinatorics   Node: 782447746ab3

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

For pairwise conflicting finite partial words, if total support size plus 2^m equals the number of words times m+1, then their volume sum is one and every support size is m or m-1, expressed without truncated subtraction.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_cube_minimum_incidence {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (s : I → Finset V) (b : I → V → Bool) (m : ℕ)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hcost : (∑ i, (s i).card) + 2^m = Fintype.card I * (m+1)) :
    (∑ i, (1 : ℚ) / 2^(s i).card) = 1 ∧
      ∀ i, (s i).card = m ∨ (s i).card + 1 = m := by
  classical
  have hu := binary_partial_word_cube_volume_bound s b hconflict
  have hc : (∑ i, ((s i).card : ℚ)) + 2^m = (Fintype.card I : ℚ) * (m+1) := by
    exact_mod_cast hcost
  have hsum : (∑ i, ((m : ℚ)+1-(s i).card)) = 2^m := by
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ]
    linarith
  have hl : (2 : ℚ)^m ≤ 2^m * ∑ i, (1 : ℚ)/2^(s i).card := by
    calc
      (2 : ℚ)^m = ∑ i, ((m : ℚ)+1-(s i).card) := hsum.symm
      _ ≤ ∑ i, (2 : ℚ)^m / 2^(s i).card :=
        sum_le_sum (fun i hi => dyadic_integer_tangent m (s i).card)
      _ = 2^m * ∑ i, (1 : ℚ)/2^(s i).card := by
        simp only [div_eq_mul_inv, one_mul, mul_sum]
  have hp : (0 : ℚ) < 2^m := by positivity
  have hv : (∑ i, (1 : ℚ)/2^(s i).card) = 1 := by nlinarith
  refine ⟨hv, ?_⟩
  have hterm : ∀ i, (m : ℚ)+1-(s i).card = 2^m / 2^(s i).card := by
    intro i
    have hle : ∀ j ∈ (univ : Finset I),
        (m : ℚ)+1-(s j).card ≤ 2^m / 2^(s j).card := by
      intro j hj
      exact dyadic_integer_tangent m (s j).card
    have heq : (∑ j, ((m : ℚ)+1-(s j).card)) = ∑ j, (2 : ℚ)^m / 2^(s j).card := by
      rw [hsum]
      simp only [div_eq_mul_inv, one_mul] at hv ⊢
      rw [← mul_sum, hv, mul_one]
    exact (sum_eq_sum_iff_of_le hle).mp heq i (mem_univ _)
  intro i
  exact (dyadic_integer_tangent_eq_iff m (s i).card).mp (hterm i)
