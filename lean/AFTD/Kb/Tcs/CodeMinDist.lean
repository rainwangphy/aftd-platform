import AFTD.Prelude

/-!
# code_min_dist

Topic: information   Node: f8c768373608

Provenance: formalization of a published result. Source: arXiv:2611.18156, Section II, line 129

Given implicit parameters n and q, for a code C : Finset (Fin n → Fin q) and natural number d, code_min_dist C d holds if there exist distinct codewords x, y ∈ C with hammingDist x y = d, and for all distinct codewords x, y ∈ C, d ≤ hammingDist x y.
-/

/-- The minimum distance of a code C is d if there are distinct codewords at distance d and no two distinct codewords have distance strictly less than d. -/
def code_min_dist {n q : ℕ} (C : Finset (Fin n → Fin q)) (d : ℕ) : Prop := (∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d) ∧
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y)
