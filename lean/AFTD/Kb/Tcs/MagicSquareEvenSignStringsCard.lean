import AFTD.Prelude

/-!
# magic_square_even_sign_strings_card

Topic: quantum   Node: 49a2867cbdfe

Provenance: helper lemma. Sanity lemma for magic_square_strategy_valid (arXiv:2610.12001 (Exact value and rigidity of the 2x3 magic rectangle), Eq. (3): four even strings).

Sanity check of the encoding of Alice's legal answers: exactly 4 of the 8 sign strings of length 3 have an even number of -1 signs (product +1).
-/

theorem magic_square_even_sign_strings_card :
    (Finset.univ.filter (fun s : Fin 3 → Bool => xor (xor (s 0) (s 1)) (s 2) = false)).card = 4 := by
  decide
