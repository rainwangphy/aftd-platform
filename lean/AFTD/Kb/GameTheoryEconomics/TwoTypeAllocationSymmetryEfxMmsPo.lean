import AFTD.Prelude

/-!
# two_type_allocation_symmetry_efx_mms_po

Topic: fair_division   Node: ce6649a8403a

Provenance: helper lemma. step towards two_type_goods_simultaneous_efx_mms_pareto

Interchanging good type A and good type B preserves feasibility, EFX fairness, exact MMS fairness, and Pareto optimality in a two-type goods instance.
-/

/-- Interchanging good type A and good type B preserves feasibility, EFX, MMS, and Pareto optimality. -/
theorem two_type_allocation_symmetry_efx_mms_po (n a b : ℕ) (p q : Fin n → ℝ) (x y : Fin n → ℕ)
    (h_feas : (∑ i, x i = a) ∧ (∑ i, y i = b))
    (h_efx : ∀ i j : Fin n,
      (0 < x j → p i * (x j : ℝ) + q i * (y j : ℝ) - p i ≤ p i * (x i : ℝ) + q i * (y i : ℝ)) ∧
      (0 < y j → p i * (x j : ℝ) + q i * (y j : ℝ) - q i ≤ p i * (x i : ℝ) + q i * (y i : ℝ)))
    (h_mms : ∀ i : Fin n, ∀ u v : Fin n → ℕ, (∑ j, u j = a) → (∑ j, v j = b) →
      ∃ j, p i * (u j : ℝ) + q i * (v j : ℝ) ≤ p i * (x i : ℝ) + q i * (y i : ℝ))
    (h_po : ¬ ∃ x' y' : Fin n → ℕ, (∑ i, x' i = a) ∧ (∑ i, y' i = b) ∧
      (∀ i : Fin n, p i * (x i : ℝ) + q i * (y i : ℝ) ≤ p i * (x' i : ℝ) + q i * (y' i : ℝ)) ∧
      (∃ i : Fin n, p i * (x i : ℝ) + q i * (y i : ℝ) < p i * (x' i : ℝ) + q i * (y' i : ℝ))) :
    ((∑ i, y i = b) ∧ (∑ i, x i = a)) ∧
    (∀ i j : Fin n,
      (0 < y j → q i * (y j : ℝ) + p i * (x j : ℝ) - q i ≤ q i * (y i : ℝ) + p i * (x i : ℝ)) ∧
      (0 < x j → q i * (y j : ℝ) + p i * (x j : ℝ) - p i ≤ q i * (y i : ℝ) + p i * (x i : ℝ))) ∧
    (∀ i : Fin n, ∀ v u : Fin n → ℕ, (∑ j, v j = b) → (∑ j, u j = a) →
      ∃ j, q i * (v j : ℝ) + p i * (u j : ℝ) ≤ q i * (y i : ℝ) + p i * (x i : ℝ)) ∧
    (¬ ∃ y' x' : Fin n → ℕ, (∑ i, y' i = b) ∧ (∑ i, x' i = a) ∧
      (∀ i : Fin n, q i * (y i : ℝ) + p i * (x i : ℝ) ≤ q i * (y' i : ℝ) + p i * (x' i : ℝ)) ∧
      (∃ i : Fin n, q i * (y i : ℝ) + p i * (x i : ℝ) < q i * (y' i : ℝ) + p i * (x' i : ℝ))) := by
  refine ⟨⟨h_feas.2, h_feas.1⟩, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨fun hj => by simpa only [add_comm] using (h_efx i j).2 hj,
           fun hj => by simpa only [add_comm] using (h_efx i j).1 hj⟩
  · intro i v u hv hu
    have := h_mms i u v hu hv
    simpa only [add_comm] using this
  · rintro ⟨y', x', hy', hx', hge, i, hlt⟩
    exact h_po ⟨x', y', hx', hy',
      by simpa only [add_comm] using hge,
      ⟨i, by simpa only [add_comm] using hlt⟩⟩
