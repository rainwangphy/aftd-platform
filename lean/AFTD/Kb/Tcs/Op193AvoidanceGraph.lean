import AFTD.Prelude

/-!
# op_193_avoidance_graph

Topic: graphs   Node: 2445015e9c66

Provenance: helper lemma. Clique construction for the anchor-avoidance reduction of OP-193.

For a family of cycle-vertex sets, there is a graph whose edges are noncycle pairs not contained in any family member; each k-clique is a stable k-set meeting every family member in at most one point.
-/

namespace Inbox777Avoid
variable (m q : ℕ) (A : Fin q → Finset (Fin m))
def graph : SimpleGraph (Fin m) where
  Adj x y := x ≠ y ∧ ¬(SimpleGraph.cycleGraph m).Adj x y ∧ ∀ j, ¬(x ∈ A j ∧ y ∈ A j)
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_, ?_⟩
    · intro hxy; exact h.2.1 hxy.symm
    · intro j hxy; exact h.2.2 j ⟨hxy.2, hxy.1⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

theorem clique_avoids (k : ℕ) (S : Finset (Fin m)) (hs : (graph m q A).IsNClique k S) :
    S.card = k ∧ (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m)) ∧
      ∀ j, (S ∩ A j).card ≤ 1 := by
  refine ⟨hs.card_eq, ?_, ?_⟩
  · intro x hx y hy hxy hxy'
    exact ((hs.isClique hx hy hxy).2.1) hxy'
  · intro j
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hxS := (Finset.mem_inter.mp hx).1
    have hyS := (Finset.mem_inter.mp hy).1
    have hxA := (Finset.mem_inter.mp hx).2
    have hyA := (Finset.mem_inter.mp hy).2
    exact ((hs.isClique hxS hyS hxy).2.2 j) ⟨hxA,hyA⟩
end Inbox777Avoid

theorem op_193_avoidance_graph (m q k : ℕ) (A : Fin q → Finset (Fin m)) :
    ∃ G : SimpleGraph (Fin m),
      (∀ x y, G.Adj x y ↔ x ≠ y ∧ ¬ (SimpleGraph.cycleGraph m).Adj x y ∧
        ∀ j, ¬(x ∈ A j ∧ y ∈ A j)) ∧
      ∀ S : Finset (Fin m), G.IsNClique k S →
        S.card = k ∧ (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m)) ∧
        ∀ j, (S ∩ A j).card ≤ 1 := by
  exact ⟨Inbox777Avoid.graph m q A, (by intros; rfl), Inbox777Avoid.clique_avoids m q A k⟩
