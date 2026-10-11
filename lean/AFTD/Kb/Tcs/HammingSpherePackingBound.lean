import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBallNonIntersect
import AFTD.Kb.Tcs.HammingBallCardEqZero
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero

/-!
# hamming_sphere_packing_bound

Topic: information   Node: cf79ceeaacc5

Provenance: formalization of a published result. Source: Cover & Thomas, Elements of Information Theory, Ch. 7; Hamming 1950

Hamming (sphere-packing) bound. Let alpha be a finite field with at least one element, and let C be a code of length n over alpha with minimum Hamming distance d > 0. Then the product of the code size card C and the volume of the Hamming ball of radius (d - 1) / 2 around the zero codeword is at most (card alpha) ^ n.
-/

/-- Hamming (sphere-packing) bound: the cardinality of any code of minimum distance d multiplied by the volume of a ball of packing radius (d-1)/2 is at most the total number of words. -/
theorem hamming_sphere_packing_bound {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] {n : ℕ} (C : ErrorCorrectingCodes.Codeword.Code n α) (d : ℕ)
    (h : ErrorCorrectingCodes.Codeword.distance C d) (hd : 0 < d) :
    C.card * (ErrorCorrectingCodes.Codeword.hamming_ball ((d - 1) / 2) (ErrorCorrectingCodes.Codeword.zero : ErrorCorrectingCodes.Codeword n α)).card ≤ (Fintype.card α) ^ n := by
  open Finset in
  have hfloor : ⌊((d : ℝ) - 1) / 2⌋₊ = (d - 1) / 2 := by
    have h1 : (d : ℝ) - 1 = ((d - 1 : ℕ) : ℝ) := (Nat.cast_pred hd).symm
    rw [h1]
    exact Nat.floor_div_eq_div (d - 1) 2
  have hdisj : (↑C : Set (ErrorCorrectingCodes.Codeword n α)).PairwiseDisjoint
      (fun c => ErrorCorrectingCodes.Codeword.hamming_ball ((d - 1) / 2) c) := by
    intro c₁ hc₁ c₂ hc₂ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro c' hc'
    rw [← hfloor] at hc' ⊢
    rw [Finset.mem_coe] at hc₁ hc₂
    exact ErrorCorrectingCodes.Codeword.hamming_ball_non_intersect C h hd c₁ c₂ ⟨hc₁, hc₂, hne⟩ c' hc'
  have h_card_union := Finset.card_biUnion (s := C)
    (t := fun c => ErrorCorrectingCodes.Codeword.hamming_ball ((d - 1) / 2) c) hdisj
  have h_sum_eq : (∑ c ∈ C, (ErrorCorrectingCodes.Codeword.hamming_ball ((d - 1) / 2) c).card) =
      C.card * (ErrorCorrectingCodes.Codeword.hamming_ball ((d - 1) / 2) (ErrorCorrectingCodes.Codeword.zero : ErrorCorrectingCodes.Codeword n α)).card := by
    have : ∀ c ∈ C, (ErrorCorrectingCodes.Codeword.hamming_ball ((d - 1) / 2) c).card =
        (ErrorCorrectingCodes.Codeword.hamming_ball ((d - 1) / 2) (ErrorCorrectingCodes.Codeword.zero : ErrorCorrectingCodes.Codeword n α)).card := by
      intro c _
      exact hamming_ball_card_eq_zero ((d - 1) / 2) c
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  rw [← h_sum_eq, ← h_card_union]
  have h_le := (C.biUnion (fun c => ErrorCorrectingCodes.Codeword.hamming_ball ((d - 1) / 2) c)).card_le_univ
  have h_total : Fintype.card (ErrorCorrectingCodes.Codeword n α) = (Fintype.card α) ^ n := by
    change Fintype.card (Fin n → α) = (Fintype.card α) ^ n
    simp
  rw [h_total] at h_le
  exact h_le
