import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine

/-!
# not_straight_line_inter_unit_sphere_card_le_two

Topic: fair_division   Node: 7eebbe574fb3

Provenance: original. Related work: refutes `straight_line_inter_unit_sphere_card_le_two`

The statement `straight_line_inter_unit_sphere_card_le_two` is false: In Lean, `Metric.sphere (0 : ℝ × ℝ) 1` is the sphere for the default product metric on `ℝ × ℝ`, whose norm is the sup norm `‖(x,y)‖ = max |x| |y|` (this is `Prod.norm_def` / `Prod.dist_eq`; there is no `InnerProductSpace ℝ (ℝ × ℝ)` instance). Hence the "unit sphere" is the boundary of the square `max(|x|,|y|) = 1`, not the Euclidean circle. The point `(1,1)` satisfies `max 1 1 = 1` so lies on it, and the straight line `y = 1` (given by the affine functional `p ↦ p.2 - 1`, whose linear part is nonzero) meets it in the whole segment `{(x,1) : |x| ≤ 1}`, which is infinite. Concretely the three distinct points `(0,1)`, `(1,1)`, `(-1,1)` all lie on both the line and the "unit sphere", so no finite set of cardinality ≤ 2 contains all intersection points. The theorem would be true for the Euclidean circle, e.g. stated for `EuclideanSpace ℝ (Fin 2)`.
-/

theorem not_straight_line_inter_unit_sphere_card_le_two : ¬ (∀ (L : StraightLine), ∃ (s : Finset (ℝ × ℝ)), s.card ≤ 2 ∧
      ∀ p ∈ Metric.sphere (0 : ℝ × ℝ) 1, L.cut p = 0 → p ∈ s) := by
  intro h
  let L : StraightLine :=
    { cut := AffineMap.mk' (fun p : ℝ × ℝ => p.2 - 1) (LinearMap.snd ℝ ℝ ℝ) 0 (by
        intro p; simp [sub_eq_add_neg])
      linear_ne_zero := by
        intro hh
        have := congrArg (fun f : (ℝ × ℝ) →ₗ[ℝ] ℝ => f (0, 1)) hh
        simp [LinearMap.snd] at this }
  obtain ⟨s, hcard, hmem⟩ := h L
  have hp0 : ((0:ℝ), (1:ℝ)) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_sphere, Prod.dist_eq]; norm_num
  have hp1 : ((1:ℝ), (1:ℝ)) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_sphere, Prod.dist_eq]; norm_num
  have hpm : ((-1:ℝ), (1:ℝ)) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_sphere, Prod.dist_eq]; norm_num
  have hc : ∀ p : ℝ × ℝ, L.cut p = p.2 - 1 := by
    intro p; simp [L]
  have h0 : ((0:ℝ), (1:ℝ)) ∈ s := hmem _ hp0 (by rw [hc]; norm_num)
  have h1 : ((1:ℝ), (1:ℝ)) ∈ s := hmem _ hp1 (by rw [hc]; norm_num)
  have hm : ((-1:ℝ), (1:ℝ)) ∈ s := hmem _ hpm (by rw [hc]; norm_num)
  have hsub : ({((0:ℝ), (1:ℝ)), ((1:ℝ), (1:ℝ)), ((-1:ℝ), (1:ℝ))} : Finset (ℝ × ℝ)) ⊆ s := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact hm
  have hc3 : ({((0:ℝ), (1:ℝ)), ((1:ℝ), (1:ℝ)), ((-1:ℝ), (1:ℝ))} : Finset (ℝ × ℝ)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals norm_num
  have := Finset.card_le_card hsub
  omega
