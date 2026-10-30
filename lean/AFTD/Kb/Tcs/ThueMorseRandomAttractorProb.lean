import AFTD.Prelude
import AFTD.Kb.Tcs.IsStringAttractor
import AFTD.Kb.Tcs.ThueMorseWord

/-!
# thue_morse_random_attractor_prob

Topic: combinatorics   Node: f8fdf7a7e0f0

Provenance: formalization of a published result. Source: arXiv:2610.10950

For natural numbers n and k, the real number defined as the ratio whose numerator is the cardinality of the finset of functions f : Fin k → {p : ℕ // p ∈ Finset.Icc 1 (2^n)} whose image { (f i).val | i : Fin k } satisfies is_string_attractor (thue_morse_word n), and whose denominator is (2^n : ℝ)^k.
-/

/-- The fraction of ordered k-tuples of positions from {1,...,2^n} whose distinct values form a string attractor of t_n. -/
noncomputable def thue_morse_random_attractor_prob (n k : ℕ) : ℝ :=
  open scoped Classical in
  let positions : Finset ℕ := Finset.Icc 1 (2^n)
  ((Finset.univ.filter (fun (f : Fin k → {p : ℕ // p ∈ positions}) =>
    is_string_attractor (thue_morse_word n) (Finset.image (fun i => (f i).val) Finset.univ))).card : ℝ) /
    ((2^n : ℝ) ^ k)
