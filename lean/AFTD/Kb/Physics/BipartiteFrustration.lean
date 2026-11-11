import AFTD.Prelude

/-!
# bipartite_frustration

Topic: statistical_mechanics   Node: 00d79c63df12

Provenance: original. Related work: folklore

The bipartite frustration index f(G) of a finite graph G is the minimum number of edges whose deletion makes G bipartite, or equivalently the minimum number of monochromatic edges over all 2-colorings of V.
-/

/-- The frustration index (or bipartite edge deletion number) of a finite graph G: the minimum number of monochromatic edges over all 2-colorings of the vertices, equal to |E| - maxcut(G). -/
def bipartite_frustration {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := Finset.univ.inf' ⟨fun _ => true, Finset.mem_univ _⟩ fun c : V → Bool =>
    (G.edgeFinset.filter fun e =>
      Sym2.lift ⟨fun u v => c u == c v, fun _ _ => by dsimp; rw [Bool.beq_comm]⟩ e).card
