import AFTD.Prelude
import AFTD.Kb.Tcs.FourVertexCycleCostPotential

/-!
# four_vertex_balanced_cost_nonneg

Topic: graphs   Node: 41b15b072681

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

On four vertices, a balanced edge weighting, nonnegative away from the diagonal, assigns nonnegative total cost whenever every closed four-step walk has nonnegative cost and loops cost zero.
-/

theorem four_vertex_balanced_cost_nonneg (w c : Fin 4 → Fin 4 → ℝ)
    (hw : ∀ i j, i ≠ j → 0 ≤ w i j)
    (hb : ∀ i, ∑ j, w i j = ∑ j, w j i)
    (hd : ∀ i, c i i = 0)
    (hc : ∀ i j k l, 0 ≤ c i j + c j k + c k l + c l i) :
    0 ≤ ∑ i, ∑ j, w i j * c i j := by
  obtain ⟨p, hp⟩ := four_vertex_cycle_cost_potential c hd hc
  have hcancel : (∑ i, ∑ j, w i j * (p i - p j)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    calc
      (∑ i, ∑ j, w i j * p i) = ∑ i, (∑ j, w i j) * p i := by
        simp_rw [Finset.sum_mul]
      _ = ∑ i, (∑ j, w j i) * p i := by simp_rw [hb]
      _ = ∑ i, ∑ j, w j i * p i := by simp_rw [Finset.sum_mul]
      _ = ∑ i, ∑ j, w i j * p j := Finset.sum_comm
  have hnn : 0 ≤ ∑ i, ∑ j, w i j * (c i j + (p i - p j)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      by_cases hij : i = j
      · subst j; simp only [hd, sub_self, add_zero, mul_zero, le_refl]
      · exact mul_nonneg (hw i j hij) (by linarith only [hp i j])
  simp_rw [mul_add, Finset.sum_add_distrib] at hnn
  simpa only [hcancel, add_zero] using hnn
