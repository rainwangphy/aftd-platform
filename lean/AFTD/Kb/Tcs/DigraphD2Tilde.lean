import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphD2TildeVertex
import AFTD.Kb.Tcs.DigraphD2TildeAdjBool

/-!
# digraph_d2_tilde

Topic: combinatorics   Node: e653c5aaaa6f

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 5

The directed graph D̃₂ represented as a bundled Digraph DigraphD2TildeVertex with adjacency relation fun a b => digraph_d2_tilde_adj_bool a b = true.
-/

/-- The directed graph D̃₂ obtained from D₂ by adding edge u₁ → u₂. -/
def digraph_d2_tilde : Digraph DigraphD2TildeVertex where Adj a b := digraph_d2_tilde_adj_bool a b = true
