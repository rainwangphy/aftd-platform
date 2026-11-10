import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# q_ary_subsequence_num_embeddings

Topic: information   Node: ea2fb94a296e

Provenance: formalization of a published result. Source: arXiv:2611.01064, Section 2; arXiv:2407.10026

For words u of length m and w of length n over an alphabet of size q represented by Fin q, q_ary_subsequence_num_embeddings q m n u w is the number of strictly increasing maps f from Fin m to Fin n such that w (f i) = u i for all i.
-/

/-- Number of strictly increasing index embeddings from Fin m to Fin n spelling u from w over Fin q. -/
def q_ary_subsequence_num_embeddings (q m n : ℕ) (u : Fin m → Fin q) (w : Fin n → Fin q) : ℕ := (Finset.univ.filter (fun f : Fin m → Fin n => StrictMono f ∧ ∀ i, w (f i) = u i)).card
