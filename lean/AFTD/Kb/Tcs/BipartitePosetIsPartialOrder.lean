import AFTD.Prelude
import AFTD.Kb.Tcs.BipartitePosetLe

/-!
# bipartite_poset_is_partial_order

Topic: combinatorics   Node: 3429a163237c

Provenance: helper lemma. arXiv:2610.24774, Section 4.1

If A and B are disjoint subsets of α, then for any simple graph H on α, the relation bipartite_poset_le H A B is a partial order on α.
-/

/-- The relation bipartite_poset_le is a partial order whenever A and B are disjoint. -/
theorem bipartite_poset_is_partial_order {α : Type*} (H : SimpleGraph α) (A B : Set α)
    (hdisj : Disjoint A B) :
    IsPartialOrder α (bipartite_poset_le H A B) := by
  have hrefl : Std.Refl (bipartite_poset_le H A B) := by
    refine Std.Refl.mk ?_
    intro x
    exact Or.inl rfl
  have htrans : IsTrans α (bipartite_poset_le H A B) := by
    refine IsTrans.mk ?_
    intro x y z hxy hyz
    rw [bipartite_poset_le] at hxy hyz ⊢
    rcases hxy with rfl | ⟨hxA, hyB, hxyadj⟩
    · exact hyz
    · rcases hyz with rfl | ⟨hyA, hzB, hyzadj⟩
      · exact Or.inr ⟨hxA, hyB, hxyadj⟩
      · exact False.elim ((Set.disjoint_left.mp hdisj) hyA hyB)
  have hanti : Std.Antisymm (bipartite_poset_le H A B) := by
    refine Std.Antisymm.mk ?_
    intro x y hxy hyx
    rw [bipartite_poset_le] at hxy hyx
    rcases hxy with rfl | ⟨hxA, hyB, hxyadj⟩
    · rfl
    · rcases hyx with hEq | ⟨hyA, hxB, hyxadj⟩
      · exact hEq.symm
      · exact False.elim ((Set.disjoint_left.mp hdisj) hyA hyB)
  exact @IsPartialOrder.mk α (bipartite_poset_le H A B)
    (@IsPreorder.mk α (bipartite_poset_le H A B) hrefl htrans) hanti
