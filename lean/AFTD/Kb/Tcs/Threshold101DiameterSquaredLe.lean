import AFTD.Prelude
import AFTD.Kb.Tcs.Threshold101Coords

/-!
# threshold101_diameter_squared_le

Topic: combinatorics   Node: 13ae44dd9e75

Provenance: helper lemma. Helper for arXiv:2610.28828 Theorem 2. Exact 101-point coordinates and a trimmed witness subgraph from https://github.com/vsvor/Gale-conjecture/tree/bd6dc9594c589791f599a0bf4685841bcb5b4486/best_known/3d_101p_088928. points.csv SHA256 362e063b96d5075c6904446d3e9164879b47233de32158e46ff6703c96704093. Independent integer geometry and SAT check: experiment 6995; the LRAT proof is independently generated and kernel checked.

Every squared distance between integer triples is at most 100000000000000100 squared.
-/

theorem threshold101_diameter_squared_le :
    ∀ i j : Fin 101, (∑ k : Fin 3, (threshold101_coords i k - threshold101_coords j k)^2) ≤ (100000000000000100 : ℤ)^2 := by
  set_option maxRecDepth 100000 in
    decide
