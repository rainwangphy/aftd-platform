import AFTD.Prelude

/-!
# ccz_induced_edges

Topic: quantum_mechanics   Node: 45035cdfd3d6

Provenance: original. Related work: folklore

For a simple graph G on a finite type V and a vertex subset S, ccz_induced_edges G S is the set of edges of G both of whose endpoints lie in S.
-/

/-- The set of edges in G induced by a vertex subset S. -/
def ccz_induced_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) := G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)
