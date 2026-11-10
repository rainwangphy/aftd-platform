import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# qary_deletion_num_embeddings

Topic: information   Node: 97fcfe559c53

Provenance: formalization of a published result. Source: arXiv:2611.01064

For natural numbers q, k, and n, a word u of length n - k over an alphabet of size q, and a word w of length n over the same alphabet, qary_deletion_num_embeddings q k n u w is the number of strictly increasing functions f from Fin (n - k) to Fin n such that w (f i) = u i for all i.
-/

/-- Number of strictly increasing index embeddings from Fin (n - k) to Fin n spelling u in w. -/
def qary_deletion_num_embeddings (q k n : ℕ) (u : Fin (n - k) → Fin q) (w : Fin n → Fin q) : ℕ := (Finset.univ.filter (fun f : Fin (n - k) → Fin n => StrictMono f ∧ ∀ i, w (f i) = u i)).card
