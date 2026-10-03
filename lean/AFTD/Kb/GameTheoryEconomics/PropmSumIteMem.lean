import AFTD.Prelude

/-!
# propm_sum_ite_mem

Topic: fair_division   Node: 66efeeba8fde

Summing an indicator of K over a superset B gives the sum over K.
-/

/-- Summing an indicator of `K ⊆ B` over `B` gives the sum over `K`. -/
lemma propm_sum_ite_mem {m : ℕ} (B K : Finset (Fin m)) (hK : K ⊆ B) (f : Fin m → ℝ) :
    ∑ e ∈ B, (if e ∈ K then f e else 0) = ∑ e ∈ K, f e := by
  classical
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hK]
