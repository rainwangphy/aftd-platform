import AFTD.Prelude
import AFTD.Kb.Tcs.SeidelMatrixCodegreeEq
import AFTD.Kb.Tcs.SeidelMatrixComplCodegreeEq
import AFTD.Kb.Tcs.SeidelMatrix

/-!
# seidel_codegree_bounds_254

Topic: combinatorics   Node: 56bb6cbbf573

Provenance: helper lemma. step towards op_605_ramsey_b63_b64_graph_exists

For any simple graph G on 254 vertices with decidable adjacency whose Seidel matrix S has all row sums equal to 1 and (S^2)_{ij} ≤ 0 for all distinct vertices i ≠ j, every adjacent pair in G has at most 62 common neighbors, and every distinct non-adjacent pair has at most 63 common neighbors in the complement graph Gᶜ.
-/

/-- For any simple graph G on 254 vertices with decidable adjacency whose Seidel matrix has all row sums 1 and non-positive off-diagonal square entries, the codegree in G of any adjacent pair is at most 62, and the codegree in Gᶜ of any distinct non-adjacent pair is at most 63. -/
theorem seidel_codegree_bounds_254
    (G : SimpleGraph (Fin 254)) [DecidableRel G.Adj]
    (h_row : ∀ i : Fin 254, ∑ j : Fin 254, seidel_matrix G i j = 1)
    (h_sq : ∀ i j : Fin 254, i ≠ j → (seidel_matrix G * seidel_matrix G) i j ≤ 0) :
    (∀ u v : Fin 254, G.Adj u v → Fintype.card (G.commonNeighbors u v) ≤ 62) ∧
    (∀ u v : Fin 254, u ≠ v → ¬ G.Adj u v → Fintype.card (Gᶜ.commonNeighbors u v) ≤ 63) := by
  constructor
  · intro u v huv
    have h := seidel_matrix_codegree_eq G u v huv
    have h1 := h_row u
    have h2 := h_row v
    have h3 := h_sq u v huv.ne
    simp only [Fintype.card_fin] at h
    omega
  · intro u v hne hna
    have hcomp : Gᶜ.Adj u v := by
      rw [SimpleGraph.compl_adj]; exact ⟨hne, hna⟩
    have h := seidel_matrix_compl_codegree_eq G u v hcomp
    have h1 := h_row u
    have h2 := h_row v
    have h3 := h_sq u v hne
    simp only [Fintype.card_fin] at h
    omega
