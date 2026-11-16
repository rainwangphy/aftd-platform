import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteUniformHypergraphSchmidtRankKTwo

/-!
# complete_uniform_hypergraph_schmidt_rank_one_one_two

Topic: quantum   Node: 8283e5fbb912

Provenance: formalization of a published result. Source: OP-1672

The rank over the rationals of the 2 by 2 matrix with entries (-1)^(Nat.choose (i + j) 2) for i, j ∈ {0, 1} is equal to 2.
-/

/-- For a = 1, b = 1, and k = 2, the 2 x 2 matrix has rational rank 2. -/
theorem complete_uniform_hypergraph_schmidt_rank_one_one_two :
    Matrix.rank (fun (i : Fin 2) (j : Fin 2) => (-1 : ℚ) ^ (Nat.choose (i.val + j.val) 2)) = 2 := complete_uniform_hypergraph_schmidt_rank_k_two 1 1 le_rfl le_rfl
