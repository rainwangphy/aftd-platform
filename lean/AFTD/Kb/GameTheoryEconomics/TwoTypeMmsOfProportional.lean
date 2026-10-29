import AFTD.Prelude

/-!
# two_type_mms_of_proportional

Topic: fair_division   Node: b7510ca66da3

Provenance: helper lemma. step towards two_type_goods_simultaneous_efx_mms_pareto

For any agent whose bundle value is at least their proportional share (p a + q b)/n, that bundle satisfies the MMS guarantee against any valid n-partition of a and b goods.
-/

/-- For any agent whose bundle value is at least their proportional share (p a + q b)/n, that bundle satisfies the exact MMS guarantee against any valid n-partition of a and b goods. -/
theorem two_type_mms_of_proportional (n a b : ℕ) (hn : 0 < n) (p q : ℝ) (x y : ℕ)
    (h_prop : p * (a : ℝ) + q * (b : ℝ) ≤ (n : ℝ) * (p * (x : ℝ) + q * (y : ℝ)))
    (u v : Fin n → ℕ) (hu : ∑ j, u j = a) (hv : ∑ j, v j = b) :
    ∃ j : Fin n, p * (u j : ℝ) + q * (v j : ℝ) ≤ p * (x : ℝ) + q * (y : ℝ) := by
  by_contra! h
  have h_sum : ∑ j : Fin n, (p * (x : ℝ) + q * (y : ℝ)) < ∑ j : Fin n, (p * (u j : ℝ) + q * (v j : ℝ)) := by
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => h j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_sum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Nat.cast_sum, ← Nat.cast_sum, hu, hv] at h_sum
  linarith
