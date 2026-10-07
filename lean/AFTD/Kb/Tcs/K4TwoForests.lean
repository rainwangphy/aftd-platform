import AFTD.Prelude
import AFTD.Kb.Tcs.K4Forest

/-!
# k4_two_forests

Topic: combinatorics   Node: 1121564738aa

Provenance: helper lemma. arXiv:2610.07318 (A note on the list chromatic number of two matroids), Claim 2.1 (two complementary 3-edge sets of K₄ are both spanning trees iff exactly one opposite pair is split), in the form used in the proof of Theorem 1.1

If the six edges of K₄ are 2-colored so that both color classes are forests and the opposite pair {01, 23} is split, then the other two opposite pairs are each monochromatic and get different colors.
-/

theorem k4_two_forests (g : Fin 6 → Bool)
    (h1 : k4_forest (Finset.univ.filter fun e => g e = true))
    (h2 : k4_forest (Finset.univ.filter fun e => g e = false)) (h01 : g 0 ≠ g 1) :
    g 2 = g 3 ∧ g 4 = g 5 ∧ g 2 ≠ g 4 := by
  have key : ∀ g : Fin 6 → Bool,
      (decide ((Finset.univ.filter fun e => g e = true).card ≤ 3) &&
        (Finset.univ.filter fun e => g e = true) != {0, 2, 5} &&
        (Finset.univ.filter fun e => g e = true) != {0, 3, 4} &&
        (Finset.univ.filter fun e => g e = true) != {1, 2, 4} &&
        (Finset.univ.filter fun e => g e = true) != {1, 3, 5}) = true →
      (decide ((Finset.univ.filter fun e => g e = false).card ≤ 3) &&
        (Finset.univ.filter fun e => g e = false) != {0, 2, 5} &&
        (Finset.univ.filter fun e => g e = false) != {0, 3, 4} &&
        (Finset.univ.filter fun e => g e = false) != {1, 2, 4} &&
        (Finset.univ.filter fun e => g e = false) != {1, 3, 5}) = true →
      g 0 != g 1 → (g 2 == g 3 && g 4 == g 5 && g 2 != g 4) = true := by
    decide +kernel
  have := key g (by simpa [k4_forest, and_assoc] using h1) (by simpa [k4_forest, and_assoc] using h2)
    (by simpa using h01)
  simpa [and_assoc] using this
