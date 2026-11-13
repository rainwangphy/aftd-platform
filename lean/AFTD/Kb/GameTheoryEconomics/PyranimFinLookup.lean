import AFTD.Prelude

/-!
# pyranim_fin_lookup

Topic: combinatorial_games   Node: facb5ecb2a14

Provenance: helper lemma. step towards pyranim_card_stable_positions

For l : Fin m → Fin (m+2), pyranim_fin_lookup m l j is the ℕ-th value of l when j < m, and the default m+2 otherwise, so that sequences can be indexed by natural numbers.
-/

/-- Total ℕ-indexed lookup into a Fin-indexed sequence, with default value m+2. -/
def pyranim_fin_lookup (m : ℕ) (l : Fin m → Fin (m + 2)) (j : ℕ) : ℕ := if h : j < m then (l ⟨j, h⟩ : ℕ) else m + 2
