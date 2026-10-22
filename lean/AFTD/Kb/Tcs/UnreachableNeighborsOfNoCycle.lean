import AFTD.Prelude
import AFTD.Kb.Tcs.CycleOfReachableNeighbors

/-!
# unreachable_neighbors_of_no_cycle

Topic: graphs   Node: 1e8d02fd2c68

Provenance: helper lemma. arXiv:2610.26912: Theorem 2.22 -- Vertex Removal and Vertex-Edge Domination

If a vertex v in a simple graph G does not lie on any cycle from v to v, then any two distinct neighbors u and w of v are not reachable from each other in the induced subgraph G - v obtained by deleting v.
-/

/-- If v lies on no cycle, its distinct neighbors belong to different components of G - v. -/
lemma unreachable_neighbors_of_no_cycle {V : Type*} (G : SimpleGraph V) (v : V)
    (hno : ¬ ∃ (p : G.Walk v v), p.IsCycle) (u w : V) (hu : G.Adj v u) (hw : G.Adj v w) (hne : u ≠ w) :
    ¬ (G.induce ({v}ᶜ : Set V)).Reachable ⟨u, (G.ne_of_adj hu).symm⟩ ⟨w, (G.ne_of_adj hw).symm⟩ := fun hreach => hno (cycle_of_reachable_neighbors G v u w hu hw hne hreach)
