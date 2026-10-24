import AFTD.Prelude
import AFTD.Kb.Tcs.Op462Coords65
import AFTD.Kb.Tcs.Op462Edges65

/-!
# op462_coords65_edges_squared_ge

Topic: combinatorics   Node: 485ad10e2707

Provenance: helper lemma. Helper formalizing the known 65-point example accompanying arXiv:2610.28828, https://github.com/vsvor/Gale-conjecture/tree/bd6dc9594c589791f599a0bf4685841bcb5b4486/best_known/3d_65p_088808. Exact data and independent computation: experiment 4045. Trimmed LRAT dependency graph: experiment 4047.

Every witness edge has scaled squared distance at least 7887420401648046950672144846523981.
-/

open scoped BigOperators

theorem op462_coords65_edges_squared_ge :
    op462_edges65.all (fun e => decide ((7887420401648046950672144846523981 : ℤ) ≤ ∑ k : Fin 3, (op462_coords65 e.1 k - op462_coords65 e.2 k)^2)) = true := by
  decide
