import AFTD.Prelude

/-!
# mordell_ten_integer_norm_sum

Topic: combinatorics   Node: 5fcc7858b13d

Provenance: formalization of a published result. Source: arXiv:2611.03088 Section 5.1

The sum of squared norms of the ten integer points in the witness configuration W is 9999608174.
-/

/-- The sum of squared norms of the ten integer points in the witness configuration is 9999608174. -/
lemma mordell_ten_integer_norm_sum :
    let W : Fin 10 → ℤ × ℤ := ![(11183, 0), (-11183, 0),
      (32765, 14669), (32765, -14669), (-32765, 14669), (-32765, -14669),
      (12323, 31572), (12323, -31572), (-12323, 31572), (-12323, -31572)]
    ∑ i : Fin 10, ((W i).1 ^ 2 + (W i).2 ^ 2) = 9999608174 := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
