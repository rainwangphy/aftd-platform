import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphQuasikernelIndependentCoverAvoidsOutneighbors

/-!
# digraph_two_vertex_avoidance_obstruction_parent_adjacency

Topic: graphs   Node: 317cf2d1f30f

Provenance: helper lemma. Consequence of the independent-neighborhood avoidance construction in OP-337.

If every quasi-kernel of a finite loopless digraph contains at least one of two specified vertices, then each in-neighbor of the first vertex is distinct from and adjacent to each in-neighbor of the second.
-/

theorem digraph_two_vertex_avoidance_obstruction_parent_adjacency
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (a b x y : α)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hblocked : ∀ Q : Finset α,
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) →
      (∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) →
      a ∈ Q ∨ b ∈ Q)
    (hxa : D.Adj x a) (hyb : D.Adj y b) :
    x ≠ y ∧ (D.Adj x y ∨ D.Adj y x) := by
  classical
  by_contra h
  have hne : x ≠ y → ¬ D.Adj x y ∧ ¬ D.Adj y x := by
    intro hxy
    constructor
    · intro h1
      exact h ⟨hxy,Or.inl h1⟩
    · intro h1
      exact h ⟨hxy,Or.inr h1⟩
  have hind : ∀ u ∈ ({x,y} : Finset α), ∀ v ∈ ({x,y} : Finset α),
      u ≠ v → ¬ D.Adj u v := by
    intro u hu v hv huv hadj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact (hne huv).1 hadj
    · exact (hne (Ne.symm huv)).2 hadj
    · exact (huv rfl).elim
  obtain ⟨Q,hQind,hQcov,_,havoid⟩ :=
    digraph_quasikernel_independent_cover_avoids_outneighbors D {x,y} hind hloop
  rcases hblocked Q hQind hQcov with ha | hb
  · exact havoid a ha ⟨x,by simp,hxa⟩
  · exact havoid b hb ⟨y,by simp,hyb⟩
