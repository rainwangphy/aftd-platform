import AFTD.Prelude

/-!
# reflexive_rel_swap_is_cycle_cover

Topic: graphs   Node: 9db815a9be1c

Provenance: helper lemma. step towards reflexive_rel_symmetric_cycle_cover_quadratic_diameter

If R is reflexive and symmetric and R x y holds, then swap x y is a cycle cover of R (it maps every vertex to an R-neighbor).
-/

/-- In a reflexive and symmetric relation R, any transposition along an edge (R x y) is a cycle cover of R. -/
theorem reflexive_rel_swap_is_cycle_cover {V : Type*} [DecidableEq V]
    (R : V → V → Prop) (hR : ∀ v, R v v) (hR_symm : ∀ u v, R u v → R v u)
    {x y : V} (hxy : R x y) :
    ∀ z : V, R z (Equiv.swap x y z) := by
  intro z
  by_cases hzx : z = x
  · rw [hzx, Equiv.swap_apply_left]
    exact hxy
  · by_cases hzy : z = y
    · rw [hzy, Equiv.swap_apply_right]
      exact hR_symm x y hxy
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
      exact hR z
