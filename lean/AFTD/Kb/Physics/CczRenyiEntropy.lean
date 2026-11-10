import AFTD.Prelude
import AFTD.Kb.Physics.CczEdgeDistribution
import AFTD.Kb.Tcs.ShannonEntropy
import AFTD.Kb.Tcs.RenyiEntropy

/-!
# ccz_renyi_entropy

Topic: quantum_mechanics   Node: 66f2fb2f1026

Provenance: original. Related work: arXiv:2610.01024

For a real order α and a simple graph G on a finite type V, ccz_renyi_entropy α G is the order-α Rényi entropy of the CCZ induced-edge distribution for α ≠ 1, and the Shannon (von Neumann) entropy when α = 1.
-/

/-- The order-α Rényi entropy (or von Neumann entropy when α = 1) of the CCZ edge reduced state of G. -/
noncomputable def ccz_renyi_entropy {V : Type*} [Fintype V] [DecidableEq V]
    (α : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  if α = 1 then
    shannon_entropy (ccz_edge_distribution G)
  else
    renyi_entropy α (ccz_edge_distribution G)
