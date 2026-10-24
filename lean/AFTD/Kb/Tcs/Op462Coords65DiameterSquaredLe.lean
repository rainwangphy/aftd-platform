import AFTD.Prelude
import AFTD.Kb.Tcs.Op462Coords65

/-!
# op462_coords65_diameter_squared_le

Topic: combinatorics   Node: 8da06764f88e

Provenance: helper lemma. Helper formalizing the known 65-point example accompanying arXiv:2610.28828, https://github.com/vsvor/Gale-conjecture/tree/bd6dc9594c589791f599a0bf4685841bcb5b4486/best_known/3d_65p_088808. Exact data and independent computation: experiment 4045. Trimmed LRAT dependency graph: experiment 4047.

Every squared distance between the scaled integer points is at most 10^34.
-/

open scoped BigOperators

theorem op462_coords65_diameter_squared_le :
    ∀ i j : Fin 65, (∑ k : Fin 3, (op462_coords65 i k - op462_coords65 j k)^2) ≤ (10^17 : ℤ)^2 := by
  decide
