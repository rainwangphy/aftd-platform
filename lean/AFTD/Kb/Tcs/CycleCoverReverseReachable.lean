import AFTD.Prelude

/-!
# cycle_cover_reverse_reachable

Topic: graphs   Node: d257d1027fd0

Provenance: helper lemma. step towards simple_graph_normalized_hop_group_quadratic_word_diameter

If p is a cycle cover of a relation R on a finite type (every point is sent to an R-successor), then every image p v can reach back to v along R.
-/

/-- A cycle cover of a finite relation sends each point to a point that can reach it back. -/
theorem cycle_cover_reverse_reachable {V : Type*} [Fintype V] (R : V → V → Prop)
    (p : Equiv.Perm V) (hp : ∀ v, R v (p v)) :
    ∀ v, Relation.ReflTransGen R (p v) v := by
  intro v
  have h_iter : ∀ k, Relation.ReflTransGen R (p v) ((p^[k]) (p v)) := by
    intro k
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      rw [Function.iterate_succ']
      exact Relation.ReflTransGen.tail ih (hp ((p^[k]) (p v)))
  have h_ord : 0 < orderOf p := orderOf_pos p
  have h := h_iter (orderOf p - 1)
  have h_eq : (p^[orderOf p - 1]) (p v) = v := by
    have h1 : (p^[orderOf p - 1]) (p v) = (p^[orderOf p - 1 + 1]) v := by
      rw [Function.iterate_succ]
      rfl
    rw [Nat.sub_add_cancel h_ord] at h1
    rw [h1, ← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  rw [h_eq] at h
  exact h
