import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryEntropy
import AFTD.Kb.Physics.DephasedPathAuxGraph
import AFTD.Kb.Physics.DephasedPathFreeComponent

/-!
# dephased_path_entropy

Topic: quantum_mechanics   Node: ca42c9f5e02c

Provenance: formalization of a published result. Source: arXiv:2511.19585, Monogamy of Mutual Information in Graph States

For n : ℕ, q : Fin n → ℝ, and S : Finset (Fin n), dephased_path_entropy n q S is defined as (S.card : ℝ) - (free.card : ℝ) plus the sum over all free connected components c of dephased_path_aux_graph n S of binaryEntropy ((1 - ∏ u ∈ Finset.univ.filter (fun u => G.connectedComponentMk u = c), q u.1) / 2).
-/

/-- Entropy set function for a dephased path graph state under independent Z-flips. -/
noncomputable def dephased_path_entropy (n : ℕ) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := open scoped Classical in
  let G := dephased_path_aux_graph n S
  let free : Finset G.ConnectedComponent := Finset.univ.filter (fun c => dephased_path_free_component n S c)
  (S.card : ℝ) - (free.card : ℝ) +
    ∑ c ∈ free, binaryEntropy ((1 - ∏ u ∈ Finset.univ.filter (fun (u : S) => G.connectedComponentMk u = c), q u.1) / 2)
