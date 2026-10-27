import AFTD.Prelude

/-!
# quadratic_bent_form_three_weight

Topic: cryptography   Node: d78430d7e66e

Provenance: helper lemma. arXiv:2610.32239, Lemma 4.1

The number of inputs in (Fin 6 → ZMod 2) on which z 0 * z 1 + z 2 * z 3 + z 4 * z 5 equals 1 is 28.
-/

/-- The Hamming weight of the 6-variable quadratic form z₁z₂ + z₃z₄ + z₅z₆ is 28. -/
theorem quadratic_bent_form_three_weight :
    (Finset.filter (fun z : Fin 6 → ZMod 2 => z 0 * z 1 + z 2 * z 3 + z 4 * z 5 = 1) Finset.univ).card = 28 := by decide
