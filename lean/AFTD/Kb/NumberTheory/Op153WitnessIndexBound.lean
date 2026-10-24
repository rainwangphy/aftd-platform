import AFTD.Prelude
import AFTD.Kb.NumberTheory.Op153PositiveQuadraticEventuallyQuadraticLowerBound
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_153_witness_index_bound

Topic: elementary_number_theory   Node: 8fed044468d7

Provenance: helper lemma. step towards op_153_eventually_subexp_bound_positive_quadratic

For a degree-2 integer polynomial g strictly positive on the positive integers, every positive integer n with g(n) <= N satisfies n <= N, once N is large enough.
-/

/-- Witness indices for values of g below N are at most N: n^2 \u2264 2 g(n) and g(n) \u2264 N force n \u2264 N once N \u2265 2. -/
theorem op_153_witness_index_bound (g : Polynomial ℤ)
    (hdeg : g.degree = 2) (hpos : ∀ n : ℕ, 0 < n → 0 < g.eval (n : ℤ)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, 0 < n → g.eval (n : ℤ) ≤ (N : ℤ) → n ≤ N := by
  obtain ⟨M, hM⟩ := op_153_positive_quadratic_eventually_quadratic_lower_bound g hdeg hpos
  refine ⟨max M 2, ?_⟩
  intro N hN n hn hgn
  have hMN : M ≤ N := le_trans (Nat.le_max_left M 2) hN
  have h2N : 2 ≤ N := le_trans (Nat.le_max_right M 2) hN
  rcases Nat.lt_or_ge n M with hlt | hge
  · exact le_trans (Nat.lt_of_lt_of_le hlt hMN).le (le_refl N)
  · have h1 : (n : ℤ) ^ 2 ≤ 2 * (N : ℤ) := le_trans (hM n hge) (by linarith)
    have h2 : n ^ 2 ≤ 2 * N := by exact_mod_cast h1
    have h3 : 2 * N ≤ N * N := by nlinarith
    have h4 : n * n ≤ N * N := by
      have := le_trans h2 h3
      simpa [pow_two] using this
    exact Nat.mul_self_le_mul_self_iff.mp h4
