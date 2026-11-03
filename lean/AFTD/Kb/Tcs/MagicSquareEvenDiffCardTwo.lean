import AFTD.Prelude

/-!
# magic_square_even_diff_card_two

Topic: quantum   Node: 642577880419

Provenance: helper lemma. step towards magic_square_score_le_threshold_add_guess

Two distinct 3-bit sign strings of even parity differ in exactly two coordinates.
-/

/-- Two distinct 3-bit sign strings of even parity differ in exactly two coordinates. -/
theorem magic_square_even_diff_card_two (s k : Fin 3 → Bool)
    (hs : (s 0 ^^ s 1 ^^ s 2) = false) (hk : (k 0 ^^ k 1 ^^ k 2) = false) (hne : s ≠ k) :
    (Finset.univ.filter (fun j : Fin 3 => s j ≠ k j)).card = 2 := by
  revert hs hk hne s k
  decide
