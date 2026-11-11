import AFTD.Prelude

/-!
# qary_all_zero_word

Topic: information   Node: 58b7a799b226

Provenance: formalization of a published result. Source: arXiv:2407.10026 "Conditional entropies of k-deletion/insertion channels"

For an alphabet size q with 1 ≤ q and length n, the all-zero word is the word in Fin n → Fin q taking constant value 0 (represented by ⟨0, hq⟩ in Fin q).
-/

/-- The all-zero word of length n over an alphabet of size q ≥ 1. -/
def qary_all_zero_word (q n : ℕ) (hq : 1 ≤ q) : Fin n → Fin q := fun _ => ⟨0, hq⟩
