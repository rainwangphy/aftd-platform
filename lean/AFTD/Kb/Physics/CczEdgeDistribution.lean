import AFTD.Prelude
import AFTD.Kb.Physics.CczInducedEdges

/-!
# ccz_edge_distribution

Topic: quantum_mechanics   Node: f152465c20c4

Provenance: original. Related work: arXiv:2610.01024

For a simple graph G on a finite type V with decidable equality and decidable adjacency, and an edge subset F, ccz_edge_distribution G F is the probability that the induced edge set of a uniformly random vertex subset equals F.
-/

/-- The probability distribution of induced edge sets under a uniform random vertex subset of G. -/
noncomputable def ccz_edge_distribution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Sym2 V)) : ℝ :=
  ((Finset.univ.filter (fun S : Finset V => ccz_induced_edges G S = F)).card : ℝ) /
    (2 ^ Fintype.card V : ℝ)
