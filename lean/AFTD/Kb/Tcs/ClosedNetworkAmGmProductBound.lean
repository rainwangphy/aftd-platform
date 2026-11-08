import AFTD.Prelude

/-!
# closed_network_am_gm_product_bound

Topic: quantum   Node: 2a4a3498e0d9

Provenance: helper lemma. arXiv:2610.35838 Eq. 31-32

For any integer n ≥ 1 and any non-negative tuples x, y : Fin n → ℝ satisfying x i + y i ≤ 1 for all i, (∏ i, x i) ^ (1 / n) + (∏ i, y i) ^ (1 / n) ≤ 1.
-/

private lemma closed_network_am_gm_product_bound_geom
    (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i : Fin n, z i) ^ (1 / (n : ℝ)) ≤ (∑ i : Fin n, z i) / n := by
  have hn0 : (0:ℕ) < n := hn
  have hn0' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
  have h := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
      (fun _ => (1:ℝ)) z
      (by intro i _; norm_num)
      (by simpa using hn0')
      (by intro i _; exact hz i)
  simpa using h

/-- AM-GM inequality applied to products of normalized responses in an n-local network. -/
theorem closed_network_am_gm_product_bound
    (n : ℕ) (hn : 1 ≤ n) (x y : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : ∀ i, x i + y i ≤ 1) :
    (∏ i : Fin n, x i) ^ (1 / (n : ℝ)) +
    (∏ i : Fin n, y i) ^ (1 / (n : ℝ)) ≤ 1 := by
  have hn0 : (0:ℕ) < n := hn
  have hn0' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
  have h1 := closed_network_am_gm_product_bound_geom n hn x hx
  have h2 := closed_network_am_gm_product_bound_geom n hn y hy
  have hsum : (∑ i : Fin n, x i) + (∑ i : Fin n, y i) ≤ n := by
    have : (∑ i : Fin n, (x i + y i)) ≤ ∑ i : Fin n, (1:ℝ) :=
      Finset.sum_le_sum (fun i _ => hxy i)
    rw [Finset.sum_add_distrib] at this
    simpa using this
  have hsum' : (∑ i : Fin n, x i) / n + (∑ i : Fin n, y i) / n ≤ 1 := by
    rw [← add_div]
    rw [div_le_iff₀ hn0']
    linarith
  linarith
