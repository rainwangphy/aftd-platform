import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOrientedTwoParentCollisionLimit

/-!
# digraph_two_parent_collision_charge_card_le_one

Topic: graphs   Node: cb49f4949a15

Provenance: helper lemma. Graph-specific multiplicity-two charge bound for the OP-110 small-overlap route.

In a loopless oriented digraph with a chosen common predecessor for every arc, if two vertices have exactly two common predecessors, at most one of those predecessors can assign the same chosen predecessor to both corresponding outgoing arcs.
-/

theorem digraph_two_parent_collision_charge_card_le_one
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (choose : α → α → α)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hchoice : ∀ s t, D.Adj s t →
      D.Adj (choose s t) s ∧ D.Adj (choose s t) t)
    (a b : α)
    (hm : (Finset.univ.filter fun p => D.Adj p a ∧ D.Adj p b).card = 2) :
    (Finset.univ.filter fun p => D.Adj p a ∧ D.Adj p b ∧ choose p a = choose p b).card ≤ 1 := by
  classical
  let P : Finset α := Finset.univ.filter fun p => D.Adj p a ∧ D.Adj p b
  apply Finset.card_le_one.mpr
  intro u hu v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  by_contra hne
  have hsub : ({u,v} : Finset α) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.1, hu.2.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.1, hv.2.1⟩
  have hcard : P.card ≤ ({u,v} : Finset α).card := by
    change (Finset.univ.filter fun p => D.Adj p a ∧ D.Adj p b).card ≤ _
    rw [hm]
    simp [hne]
  have hpair : ({u,v} : Finset α) = P := Finset.eq_of_subset_of_card_le hsub hcard
  have hparents : ∀ x, D.Adj x a → D.Adj x b → x = u ∨ x = v := by
    intro x hxa hxb
    have hxP : x ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxa, hxb⟩
    rw [← hpair] at hxP
    simpa using hxP
  have hbad := digraph_oriented_two_parent_collision_limit α D choose hloop hori hchoice
    a b u v hu.1 hu.2.1 hv.1 hv.2.1 hparents
  exact hbad ⟨hu.2.2, hv.2.2⟩
