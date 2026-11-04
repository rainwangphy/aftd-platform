import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# three_deletion_num_embeddings

Topic: information   Node: 282887152b68

Provenance: formalization of a published result. Source: arXiv:2611.01064 Section 2

For a binary word w of length n and a binary word y of length n + 3, three_deletion_num_embeddings n w y is the number of strictly increasing functions f from Fin n to Fin (n + 3) such that y (f i) = w i for all i.
-/

/-- Number of length-n subword embeddings of w in a length-(n+3) host word y. -/
def three_deletion_num_embeddings (n : ℕ) (w : Fin n → Bool) (y : Fin (n + 3) → Bool) : ℕ := (Finset.univ.filter (fun f : Fin n → Fin (n + 3) => StrictMono f ∧ ∀ i, y (f i) = w i)).card
