import AFTD.Prelude

/-!
# is_rigid_sequence

Topic: combinatorics   Node: c29cf66fa0bd

Provenance: formalization of a published result. Source: arXiv:2610.35819 Definition 4.1

A sequence S over an abelian group G without an n-term zero-sum subsequence is called rigid with parameters n and m if every term of S has multiplicity n - 1 (heavy) or at most m - 1 (light), and every n-term zero-sum multiset W with support in the support of S is of the form x^n for some x in S, or h^k l^(n-k) for some heavy term h, light term l, and 0 < k < n.
-/

/-- A sequence over an abelian group without n-term zero-sum is rigid if terms are heavy (multiplicity n-1) or light (multiplicity at most m-1), and every n-term zero-sum on its support has the form x^n or h^k l^(n-k). -/
def is_rigid_sequence (n m : ℕ) {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Multiset G) : Prop := (¬ ∃ W : Multiset G, W ≤ S ∧ W.card = n ∧ W.sum = 0) ∧
  (∀ x ∈ S, S.count x = n - 1 ∨ (0 < S.count x ∧ S.count x ≤ m - 1)) ∧
  (∀ W : Multiset G, W.card = n → W.sum = 0 → (∀ x ∈ W, x ∈ S) →
    (∃ x ∈ S, W = Multiset.replicate n x) ∨
    (∃ (h l : G) (k : ℕ), S.count h = n - 1 ∧ (0 < S.count l ∧ S.count l ≤ m - 1) ∧
      0 < k ∧ k < n ∧ W = Multiset.replicate k h + Multiset.replicate (n - k) l))
