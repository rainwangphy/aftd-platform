import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# collision_embedding_pair_count

Topic: information   Node: 99680aae44e5

Provenance: helper lemma. step towards op_1003_two_insertion_collision_defect_envelope_six

For a binary word w of length m + 2, collision_embedding_pair_count m w is the number of ordered pairs (f, g) of strictly increasing maps Fin m → Fin (m + 2) that read the same word off w, i.e. w (f i) = w (g i) for all i.
-/

/-- The two-insertion collision sum rewritten as the number of ordered pairs of strictly increasing embeddings inducing equal sub-words; this is the computable form, since it avoids the outer sum over Fin m → Bool and the inner `^ 2`. -/
def collision_embedding_pair_count (m : ℕ) (w : Fin (m + 2) → Bool) : ℕ := let E := (Finset.univ : Finset (Fin m → Fin (m + 2))).filter (fun f => StrictMono f)
  ((E.product E).filter (fun p => ∀ i, w (p.1 i) = w (p.2 i))).card
