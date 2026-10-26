import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHypercube
import AFTD.Kb.Tcs.SimpleGraphLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHopMemLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# op_300_hypercube_two_leap_group_card

Topic: graphs   Node: 682e62d1e178

Provenance: formalization of a published result. Source: arXiv:2610.18463 Question 5.4

The 2-dimensional hypercube graph Q₂ (the 4-cycle C₄) has leap group of cardinality 8.
-/

/-- Vertex 00 of Q₂. -/
def op_300_hypercube_two_leap_group_card_v00 : Fin 2 → Bool := ![false, false]

/-- Vertex 01 of Q₂. -/
def op_300_hypercube_two_leap_group_card_v01 : Fin 2 → Bool := ![false, true]

/-- Vertex 11 of Q₂. -/
def op_300_hypercube_two_leap_group_card_v11 : Fin 2 → Bool := ![true, true]

/-- Vertex 10 of Q₂. -/
def op_300_hypercube_two_leap_group_card_v10 : Fin 2 → Bool := ![true, false]

/-- The rotation 00 ↦ 01 ↦ 11 ↦ 10 ↦ 00 of the 4-cycle Q₂. -/
noncomputable def op_300_hypercube_two_leap_group_card_r : Equiv.Perm (Fin 2 → Bool) :=
  Equiv.ofBijective
    (fun x => if x = op_300_hypercube_two_leap_group_card_v00 then op_300_hypercube_two_leap_group_card_v01
              else if x = op_300_hypercube_two_leap_group_card_v01 then op_300_hypercube_two_leap_group_card_v11
              else if x = op_300_hypercube_two_leap_group_card_v11 then op_300_hypercube_two_leap_group_card_v10
              else op_300_hypercube_two_leap_group_card_v00)
    (by decide)

/-- The reflection (00 01)(11 10) of the 4-cycle Q₂. -/
noncomputable def op_300_hypercube_two_leap_group_card_s : Equiv.Perm (Fin 2 → Bool) :=
  Equiv.ofBijective
    (fun x => if x = op_300_hypercube_two_leap_group_card_v00 then op_300_hypercube_two_leap_group_card_v01
              else if x = op_300_hypercube_two_leap_group_card_v01 then op_300_hypercube_two_leap_group_card_v00
              else if x = op_300_hypercube_two_leap_group_card_v11 then op_300_hypercube_two_leap_group_card_v10
              else op_300_hypercube_two_leap_group_card_v11)
    (by decide)

/-- A computable adjacency test for Q₂. -/
def op_300_hypercube_two_leap_group_card_adjB (u v : Fin 2 → Bool) : Bool :=
  (u 0 != v 0 && u 1 == v 1) || (u 0 == v 0 && u 1 != v 1)

/-- On coordinates `Fin 2`, "differs in exactly one coordinate" is a decidable condition. -/
lemma op_300_hypercube_two_leap_group_card_existsUnique_iff (u v : Fin 2 → Bool) :
    (∃! i : Fin 2, u i ≠ v i) ↔
      (u 0 ≠ v 0 ∧ u 1 = v 1) ∨ (u 0 = v 0 ∧ u 1 ≠ v 1) := by
  constructor
  · rintro ⟨a, ha, hu⟩
    fin_cases a
    · left
      exact ⟨ha, by by_contra h; exact absurd (hu 1 h) (by decide)⟩
    · right
      exact ⟨by by_contra h; exact absurd (hu 0 h) (by decide), ha⟩
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · refine ⟨0, h0, ?_⟩
      intro j hj
      fin_cases j
      · rfl
      · exact absurd h1 hj
    · refine ⟨1, h1, ?_⟩
      intro j hj
      fin_cases j
      · exact absurd h0 hj
      · rfl

/-- The adjacency test `adjB` agrees with "differs in exactly one coordinate". -/
lemma op_300_hypercube_two_leap_group_card_adjB_iff_all :
    ∀ u v : Fin 2 → Bool,
      (op_300_hypercube_two_leap_group_card_adjB u v = true ↔
        u ≠ v ∧
          (((u 0 ≠ v 0 ∧ u 1 = v 1) ∨ (u 0 = v 0 ∧ u 1 ≠ v 1)) ∨
            ((v 0 ≠ u 0 ∧ v 1 = u 1) ∨ (v 0 = u 0 ∧ v 1 ≠ u 1)))) := by
  decide

/-- `adjB` is a computable test for adjacency in Q₂. -/
lemma op_300_hypercube_two_leap_group_card_adjB_iff (u v : Fin 2 → Bool) :
    op_300_hypercube_two_leap_group_card_adjB u v = true ↔
      (simple_graph_hypercube 2).Adj u v := by
  rw [simple_graph_hypercube, SimpleGraph.fromRel_adj,
    op_300_hypercube_two_leap_group_card_existsUnique_iff,
    op_300_hypercube_two_leap_group_card_existsUnique_iff]
  exact op_300_hypercube_two_leap_group_card_adjB_iff_all u v

/-- The eight elements `{1, r, r², r³, s, sr, sr², sr³}` of `Perm Q₂`. -/
noncomputable def op_300_hypercube_two_leap_group_card_S : Finset (Equiv.Perm (Fin 2 → Bool)) :=
  {1, op_300_hypercube_two_leap_group_card_r, op_300_hypercube_two_leap_group_card_r ^ 2,
    op_300_hypercube_two_leap_group_card_r ^ 3, op_300_hypercube_two_leap_group_card_s,
    op_300_hypercube_two_leap_group_card_s * op_300_hypercube_two_leap_group_card_r,
    op_300_hypercube_two_leap_group_card_s * op_300_hypercube_two_leap_group_card_r ^ 2,
    op_300_hypercube_two_leap_group_card_s * op_300_hypercube_two_leap_group_card_r ^ 3}

lemma op_300_hypercube_two_leap_group_card_S_one_mem :
    (1 : Equiv.Perm (Fin 2 → Bool)) ∈ op_300_hypercube_two_leap_group_card_S := by decide

/-- The eight listed elements are closed under multiplication. -/
lemma op_300_hypercube_two_leap_group_card_S_mul_mem :
    ∀ a b : Equiv.Perm (Fin 2 → Bool),
      a ∈ op_300_hypercube_two_leap_group_card_S →
      b ∈ op_300_hypercube_two_leap_group_card_S →
      a * b ∈ op_300_hypercube_two_leap_group_card_S := by
  intro a b ha hb
  simp only [op_300_hypercube_two_leap_group_card_S, Finset.mem_insert,
    Finset.mem_singleton] at ha hb ⊢
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The eight listed elements are closed under inversion. -/
lemma op_300_hypercube_two_leap_group_card_S_inv_mem :
    ∀ a : Equiv.Perm (Fin 2 → Bool),
      a ∈ op_300_hypercube_two_leap_group_card_S →
      a⁻¹ ∈ op_300_hypercube_two_leap_group_card_S := by
  intro a ha
  simp only [op_300_hypercube_two_leap_group_card_S, Finset.mem_insert,
    Finset.mem_singleton] at ha ⊢
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · rw [inv_eq_of_mul_eq_one_right
      (show op_300_hypercube_two_leap_group_card_r * op_300_hypercube_two_leap_group_card_r ^ 3 = 1 by decide)]
    decide
  · rw [inv_eq_of_mul_eq_one_right
      (show op_300_hypercube_two_leap_group_card_r ^ 2 * op_300_hypercube_two_leap_group_card_r ^ 2 = 1 by decide)]
    decide
  · rw [inv_eq_of_mul_eq_one_right
      (show op_300_hypercube_two_leap_group_card_r ^ 3 * op_300_hypercube_two_leap_group_card_r = 1 by decide)]
    decide
  · rw [inv_eq_of_mul_eq_one_right
      (show op_300_hypercube_two_leap_group_card_s * op_300_hypercube_two_leap_group_card_s = 1 by decide)]
    decide
  · rw [inv_eq_of_mul_eq_one_right
      (show op_300_hypercube_two_leap_group_card_s * op_300_hypercube_two_leap_group_card_r *
          (op_300_hypercube_two_leap_group_card_r ^ 3 * op_300_hypercube_two_leap_group_card_s) = 1 by decide)]
    decide
  · rw [inv_eq_of_mul_eq_one_right
      (show op_300_hypercube_two_leap_group_card_s * op_300_hypercube_two_leap_group_card_r ^ 2 *
          (op_300_hypercube_two_leap_group_card_r ^ 2 * op_300_hypercube_two_leap_group_card_s) = 1 by decide)]
    decide
  · rw [inv_eq_of_mul_eq_one_right
      (show op_300_hypercube_two_leap_group_card_s * op_300_hypercube_two_leap_group_card_r ^ 3 *
          (op_300_hypercube_two_leap_group_card_r * op_300_hypercube_two_leap_group_card_s) = 1 by decide)]
    decide

/-- The explicit subgroup `{1, r, r², r³, s, sr, sr², sr³}` of `Perm Q₂`. -/
noncomputable def op_300_hypercube_two_leap_group_card_H :
    Subgroup (Equiv.Perm (Fin 2 → Bool)) where
  carrier := {x | x ∈ op_300_hypercube_two_leap_group_card_S}
  mul_mem' := fun ha hb => op_300_hypercube_two_leap_group_card_S_mul_mem _ _ ha hb
  one_mem' := op_300_hypercube_two_leap_group_card_S_one_mem
  inv_mem' := fun ha => op_300_hypercube_two_leap_group_card_S_inv_mem _ ha

/-- A finite check: any permutation of the four vertices of Q₂ sending every vertex to a
neighbour lies in the eight-element set. -/
lemma op_300_hypercube_two_leap_group_card_hops_b :
    ∀ x : Equiv.Perm (Fin 2 → Bool),
      (∀ v, op_300_hypercube_two_leap_group_card_adjB v (x v) = true) →
      x ∈ op_300_hypercube_two_leap_group_card_S := by
  decide

/-- Every hop of Q₂ belongs to the eight-element set. -/
lemma op_300_hypercube_two_leap_group_card_hop_mem_S
    (x : Equiv.Perm (Fin 2 → Bool))
    (hx : simple_graph_is_hop (simple_graph_hypercube 2) x) :
    x ∈ op_300_hypercube_two_leap_group_card_S :=
  op_300_hypercube_two_leap_group_card_hops_b x
    (fun v => (op_300_hypercube_two_leap_group_card_adjB_iff v (x v)).mpr (hx v))

lemma op_300_hypercube_two_leap_group_card_r_hops :
    ∀ v, op_300_hypercube_two_leap_group_card_adjB v
      (op_300_hypercube_two_leap_group_card_r v) = true := by
  decide

lemma op_300_hypercube_two_leap_group_card_s_hops :
    ∀ v, op_300_hypercube_two_leap_group_card_adjB v
      (op_300_hypercube_two_leap_group_card_s v) = true := by
  decide

/-- The rotation is a hop of Q₂. -/
lemma op_300_hypercube_two_leap_group_card_r_hop :
    simple_graph_is_hop (simple_graph_hypercube 2) op_300_hypercube_two_leap_group_card_r :=
  fun v => (op_300_hypercube_two_leap_group_card_adjB_iff v _).mp
    (op_300_hypercube_two_leap_group_card_r_hops v)

/-- The reflection is a hop of Q₂. -/
lemma op_300_hypercube_two_leap_group_card_s_hop :
    simple_graph_is_hop (simple_graph_hypercube 2) op_300_hypercube_two_leap_group_card_s :=
  fun v => (op_300_hypercube_two_leap_group_card_adjB_iff v _).mp
    (op_300_hypercube_two_leap_group_card_s_hops v)

/-- The 2-dimensional hypercube has leap group of order 8. -/
theorem op_300_hypercube_two_leap_group_card :
    Nat.card (simple_graph_leap_group (simple_graph_hypercube 2)) = 8 := by
  have hle : simple_graph_leap_group (simple_graph_hypercube 2) ≤
      op_300_hypercube_two_leap_group_card_H := by
    rw [simple_graph_leap_group]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    exact op_300_hypercube_two_leap_group_card_hop_mem_S x hx
  have hr : op_300_hypercube_two_leap_group_card_r ∈
      simple_graph_leap_group (simple_graph_hypercube 2) :=
    simple_graph_is_hop_mem_leap_group _ _ op_300_hypercube_two_leap_group_card_r_hop
  have hs : op_300_hypercube_two_leap_group_card_s ∈
      simple_graph_leap_group (simple_graph_hypercube 2) :=
    simple_graph_is_hop_mem_leap_group _ _ op_300_hypercube_two_leap_group_card_s_hop
  have hge : op_300_hypercube_two_leap_group_card_H ≤
      simple_graph_leap_group (simple_graph_hypercube 2) := by
    intro x hx
    have hxS : x ∈ op_300_hypercube_two_leap_group_card_S := hx
    simp only [op_300_hypercube_two_leap_group_card_S, Finset.mem_insert,
      Finset.mem_singleton] at hxS
    rcases hxS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hr
    · exact Subgroup.pow_mem _ hr 2
    · exact Subgroup.pow_mem _ hr 3
    · exact hs
    · exact Subgroup.mul_mem _ hs hr
    · exact Subgroup.mul_mem _ hs (Subgroup.pow_mem _ hr 2)
    · exact Subgroup.mul_mem _ hs (Subgroup.pow_mem _ hr 3)
  have hEq : simple_graph_leap_group (simple_graph_hypercube 2) =
      op_300_hypercube_two_leap_group_card_H := le_antisymm hle hge
  rw [hEq,
    show Nat.card ↥op_300_hypercube_two_leap_group_card_H =
      (op_300_hypercube_two_leap_group_card_H :
        Set (Equiv.Perm (Fin 2 → Bool))).ncard from Nat.card_coe_set_eq _]
  have hcoe : (op_300_hypercube_two_leap_group_card_H :
      Set (Equiv.Perm (Fin 2 → Bool))) = ↑op_300_hypercube_two_leap_group_card_S := rfl
  rw [hcoe, Set.ncard_coe_finset]
  decide
