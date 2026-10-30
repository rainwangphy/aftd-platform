import AFTD.Prelude

/-!
# yang_mills_resonance_polynomial

Topic: classical_fields   Node: 65ab867d9b07

Provenance: formalization of a published result. Source: arXiv:2610.36784, Eq. (2.3)-(2.5)

For each natural number m, yang_mills_resonance_polynomial m is the rational polynomial P_m in Polynomial ℚ defined as the quotient of (-1)^(m+1) * kappa divided by the monic polynomial X - 1 via Polynomial.divByMonic, where with D = 2m + 3, b_0 = 1, and for 0 <= n < m, b_{n+1} = ((n^2 - (2m+1)n + D) * b_n - D * X * sum_{i=0}^n sum_{j=0}^{n-i} b_i * b_j * b_{n-i-j}) / (2*(n+1)*(m-n)), and kappa = (-m*(m+1) + D) * b_m - D * X * sum_{i=0}^m sum_{j=0}^{m-i} b_i * b_j * b_{m-i-j}.
-/

/-- The rational resonance polynomial P_m(z) for odd spatial dimension d = 2m + 5 in self-similar Yang-Mills theory. -/
noncomputable def yang_mills_resonance_polynomial (m : ℕ) : Polynomial ℚ := open BigOperators in
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
  Polynomial.divByMonic (sign • kappa) (Polynomial.X - 1)
