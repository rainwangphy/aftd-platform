import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword

/-!
# hamming_ball_card_eq_zero

Topic: information   Node: f7d5917af094

Provenance: helper lemma. Cover & Thomas, Elements of Information Theory, Ch. 7

Translation invariance of Hamming ball size. Let alpha be a finite field, and let c be a codeword of length n over alpha. Then for any radius r, the cardinality of the Hamming ball of radius r around c equals the cardinality of the Hamming ball of radius r around the all-zero codeword.
-/

/-- Translation invariance of Hamming ball size: the size of a Hamming ball of radius r around any codeword equals the size of the Hamming ball of radius r around the all-zero codeword. -/
theorem hamming_ball_card_eq_zero {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] {n : ℕ} (r : ℕ) (c : ErrorCorrectingCodes.Codeword n α) :
    (ErrorCorrectingCodes.Codeword.hamming_ball r c).card =
      (ErrorCorrectingCodes.Codeword.hamming_ball r (ErrorCorrectingCodes.Codeword.zero : ErrorCorrectingCodes.Codeword n α)).card := by
  have h_zero : (ErrorCorrectingCodes.Codeword.zero : ErrorCorrectingCodes.Codeword n α) = 0 := rfl
  have h_sub_dist : ∀ x : ErrorCorrectingCodes.Codeword n α,
      ErrorCorrectingCodes.Codeword.hamming_distance (x - c) 0 =
        ErrorCorrectingCodes.Codeword.hamming_distance x c := by
    intro x
    dsimp [ErrorCorrectingCodes.Codeword.hamming_distance, hammingDist]
    congr 1
    ext i
    simp [sub_ne_zero]
  have h_add_dist : ∀ y : ErrorCorrectingCodes.Codeword n α,
      ErrorCorrectingCodes.Codeword.hamming_distance (y + c) c =
        ErrorCorrectingCodes.Codeword.hamming_distance y 0 := by
    intro y
    dsimp [ErrorCorrectingCodes.Codeword.hamming_distance, hammingDist]
    congr 1
    ext i
    simp
  have h_mem : ∀ (s : ℕ) (w x : ErrorCorrectingCodes.Codeword n α),
      x ∈ ErrorCorrectingCodes.Codeword.hamming_ball s w ↔
        ErrorCorrectingCodes.Codeword.hamming_distance x w ≤ s := by
    intro s w x
    simp [ErrorCorrectingCodes.Codeword.hamming_ball]
  have h_inj : Function.Injective (fun x : ErrorCorrectingCodes.Codeword n α => x - c) := by
    intro x y hxy
    simpa using congr_arg (fun z => z + c) hxy
  have h_img : (ErrorCorrectingCodes.Codeword.hamming_ball r c).image (fun x => x - c) =
      ErrorCorrectingCodes.Codeword.hamming_ball r (ErrorCorrectingCodes.Codeword.zero : ErrorCorrectingCodes.Codeword n α) := by
    ext y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [h_mem] at hx ⊢
      rw [h_zero, h_sub_dist]
      exact hx
    · intro hy
      rw [h_mem] at hy
      refine ⟨y + c, ?_, by simp⟩
      rw [h_mem, h_add_dist]
      rw [h_zero] at hy
      exact hy
  rw [← h_img]
  exact (Finset.card_image_of_injective _ h_inj).symm
