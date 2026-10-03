import AFTD.Prelude

/-!
# ef1cost_shift

Topic: fair_division   Node: 77e321641d77

For two agents and X inside Y, giving Y (instead of X) to agent p and the rest to q raises the item-wise cost sum by the sum over Y minus X of c_p - c_q.
-/

lemma ef1cost_shift {m : ℕ} (c : Fin 2 → Fin m → ℝ) (p q : Fin 2) (X Y : Finset (Fin m))
    (hXY : X ⊆ Y) :
    ∑ j, c (if j ∈ Y then p else q) j =
      ∑ j, c (if j ∈ X then p else q) j + ∑ j ∈ Y \ X, (c p j - c q j) := by
  classical
  rw [← Fintype.sum_ite_mem (Y \ X), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hX : j ∈ X
  · have hY : j ∈ Y := hXY hX
    simp [hX, hY]
  · by_cases hY : j ∈ Y
    · simp [hX, hY]
    · simp [hX, hY]
