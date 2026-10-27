import AFTD.Prelude
import AFTD.Kb.Tcs.Threshold101Coords
import AFTD.Kb.Tcs.Threshold101Edges

/-!
# threshold101_edges_squared_ge

Topic: combinatorics   Node: 27b66549a11c

Provenance: helper lemma. Helper for arXiv:2610.28828 Theorem 2. Exact 101-point coordinates and a trimmed witness subgraph from https://github.com/vsvor/Gale-conjecture/tree/bd6dc9594c589791f599a0bf4685841bcb5b4486/best_known/3d_101p_088928. points.csv SHA256 362e063b96d5075c6904446d3e9164879b47233de32158e46ff6703c96704093. Independent integer geometry and SAT check: experiment 6995; the LRAT proof is independently generated and kernel checked.

Every trimmed witness edge has integer squared length at least 7908209857886758229068357146803906.
-/

theorem threshold101_edges_squared_ge :
    threshold101_edges.all (fun e => decide ((7908209857886758229068357146803906 : ℤ) ≤ ∑ k : Fin 3, (threshold101_coords e.1 k - threshold101_coords e.2 k)^2)) = true := by
  set_option maxRecDepth 100000 in
    decide
