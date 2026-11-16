import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# petrial_nullity_poly_iso

Topic: combinatorics   Node: 61dec74ed0d9

Provenance: helper lemma. Graph reindexing helper for the OP-1239 counterexample.

Isomorphic finite simple graphs have the same partial Petrial nullity generating polynomial.
-/

theorem petrial_nullity_poly_iso {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) : petrial_nullity_poly G = petrial_nullity_poly H := by
  dsimp [petrial_nullity_poly]
  rw [Fintype.sum_equiv (Equiv.finsetCongr (e : V ≃ W))]
  intro F
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr (e : V ≃ W)
  have hmat : (Matrix.reindex (e : V ≃ W) (e : V ≃ W)) (petrial_matrix G F) =
      petrial_matrix H (F.map (e : V ≃ W).toEmbedding) := by
    dsimp [petrial_matrix]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, SimpleGraph.adjMatrix_apply, Matrix.diagonal_apply]
    simp only [Finset.mem_map_equiv]
    have h_adj : G.Adj ((e : V ≃ W).symm i) ((e : V ≃ W).symm j) ↔ H.Adj i j := by
      rw [← e.map_adj_iff]
      simp
    simp only [h_adj]
    congr 1
    simp only [EmbeddingLike.apply_eq_iff_eq]
  have hrank : (petrial_matrix H (Finset.map (e : V ≃ W).toEmbedding F)).rank =
      (petrial_matrix G F).rank := by
    rw [← hmat, Matrix.rank_reindex]
  rw [Equiv.finsetCongr_apply]
  rw [hcard, hrank]
