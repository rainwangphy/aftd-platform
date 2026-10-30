import AFTD.Prelude

/-!
# yang_mills_residual_polynomial

Topic: classical_fields   Node: 7cfc5ead758e

Provenance: formalization of a published result. Source: arXiv:2610.36784, Eq. (3.1) and Sec. 3

For each natural number m, yang_mills_residual_polynomial m is the rational polynomial S_m in Polynomial ℚ obtained as the quotient of the resonance polynomial P_m (computed as in yang_mills_resonance_polynomial m) divided by the monic quadratic polynomial X^2 + b_coeff * X + c_coeff via Polynomial.divByMonic, where d = 2m + 5, b_coeff = -2 * (d^3 - 16*d^2 + 89*d - 146) / ((d - 2)*(d - 1)^2), and c_coeff = ((d - 10)*(d - 5) / ((d - 2)*(d - 1)))^2.
-/

/-- The residual polynomial S_m(z) = P_m(z) / ((z - z_-)(z - z_+)) dividing out the explicit profile roots. -/
noncomputable def yang_mills_residual_polynomial (m : ℕ) : Polynomial ℚ := open BigOperators in
  let rec cube_sum (l : List (Polynomial ℚ)) (n : ℕ) : Polynomial ℚ :=
    ∑ i ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (n + 1 - i),
        l.getD i 0 * l.getD j 0 * l.getD (n - i - j) 0
  let rec b_list : ℕ → List (Polynomial ℚ)
    | 0 => [1]
    | n + 1 =>
      let prev := b_list n
      if n < m then
        let D : ℚ := 2 * m + 3
        let bn := prev.getD n 0
        let triple := cube_sum prev n
        let num := ((n ^ 2 - (2 * m + 1 : ℚ) * n + D : ℚ) • bn) -
                   (D • Polynomial.X * triple)
        let den : ℚ := 2 * (n + 1) * (m - n)
        prev ++ [(den⁻¹ : ℚ) • num]
      else
        prev ++ [0]
  let l := b_list m
  let D : ℚ := 2 * m + 3
  let bm := l.getD m 0
  let triple_m := cube_sum l m
  let kappa := ((-((m : ℚ) * (m + 1)) + D : ℚ) • bm) - (D • Polynomial.X * triple_m)
  let sign : ℚ := (-1 : ℚ) ^ (m + 1)
  let P : Polynomial ℚ := Polynomial.divByMonic (sign • kappa) (Polynomial.X - 1)
  let d : ℚ := 2 * m + 5
  let b_coeff : ℚ := -2 * (d^3 - 16 * d^2 + 89 * d - 146) / ((d - 2) * (d - 1)^2)
  let c_coeff : ℚ := ((d - 10) * (d - 5) / ((d - 2) * (d - 1)))^2
  let Q : Polynomial ℚ := Polynomial.X ^ 2 + (Polynomial.C b_coeff) * Polynomial.X + Polynomial.C c_coeff
  Polynomial.divByMonic P Q
