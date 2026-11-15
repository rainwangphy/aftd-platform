import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphD2TildeVertex

/-!
# digraph_d2_tilde_adj_bool

Topic: combinatorics   Node: ac4d9600e3af

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 5

Adjacency boolean function for D̃₂: directed edge from u₁ to u₂, and between uᵢ and v(ε) directed uᵢ → v(ε) if εᵢ = 1 and v(ε) → uᵢ if εᵢ = -1.
-/

/-- Boolean adjacency relation for the directed graph D̃₂. -/
def digraph_d2_tilde_adj_bool : DigraphD2TildeVertex → DigraphD2TildeVertex → Bool := fun a b =>
  match a, b with
  | .u1, .u2 => true
  | .u1, .v true _ => true
  | .v false _, .u1 => true
  | .u2, .v _ true => true
  | .v _ false, .u2 => true
  | _, _ => false
