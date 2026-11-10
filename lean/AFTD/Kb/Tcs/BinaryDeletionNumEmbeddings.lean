import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# binary_deletion_num_embeddings

Topic: information   Node: 6d97d8a3ea46

Provenance: formalization of a published result. Source: arXiv:2611.01064: Maximal input entropy for binary two-deletion and two-insertion channels

For natural numbers k and n, a binary word u of length n - k, and a binary word w of length n, binary_deletion_num_embeddings k n u w is the number of strictly increasing functions f from Fin (n - k) to Fin n such that w (f i) = u i for all i.
-/

/-- The number of index subsets of size n - k of a binary word w of length n whose retained subsequence equals u. -/
def binary_deletion_num_embeddings (k n : ℕ) (u : Fin (n - k) → Bool) (w : Fin n → Bool) : ℕ := (Finset.univ.filter (fun f : Fin (n - k) → Fin n => StrictMono f ∧ ∀ i, w (f i) = u i)).card
