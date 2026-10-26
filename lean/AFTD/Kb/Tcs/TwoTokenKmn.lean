import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph

/-!
# two_token_kmn

Topic: graphs   Node: d457d2826cbc

Provenance: formalization of a published result. Source: arXiv:2610.28936 Definition 2.5

The 2-token graph F_2(K_{m,n}) of the complete bipartite graph K_{m,n}.
-/

/-- The 2-token graph of the complete bipartite graph K_{m,n}. -/
abbrev two_token_kmn (m n : ℕ) : SimpleGraph { s : Finset (Fin m ⊕ Fin n) // s.card = 2 } := token_graph (completeBipartiteGraph (Fin m) (Fin n)) 2
