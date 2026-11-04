import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# two_deletion_num_embeddings

Topic: information   Node: f3621ab128a3

Provenance: formalization of a published result. Source: arXiv:2611.01064, Section 2

For a binary word w of length n and y of length n + 2, two_deletion_num_embeddings n w y is the number of strictly increasing index embeddings from Fin n into Fin (n + 2) that select w as a subword of y.
-/

/-- Number of subsequence embeddings of a binary word of length n into a word of length n + 2. -/
def two_deletion_num_embeddings (n : ℕ) (w : Fin n → Bool) (y : Fin (n + 2) → Bool) : ℕ := (Finset.univ.filter (fun f : Fin n → Fin (n + 2) => StrictMono f ∧ ∀ i, y (f i) = w i)).card
