import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeDeletionNumEmbeddings

/-!
# three_deletion_num_embeddings_one_zero

Topic: information   Node: e984c26689fa

Provenance: helper lemma. folklore

The binary word of length 1 constantly equal to false has exactly 4 embeddings in the binary word of length 4 constantly equal to false.
-/

/-- Sanity check: the 1-bit word [0] has 4 embeddings in the 4-bit word [0,0,0,0]. -/
theorem three_deletion_num_embeddings_one_zero : three_deletion_num_embeddings 1 (fun _ => false) (fun _ => false) = 4 := by
  decide
