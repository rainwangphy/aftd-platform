import AFTD.Prelude

/-!
# harborth_bound_equality_rank_three_implies_six

Topic: combinatorics   Node: 05d92a6060bc

Provenance: helper lemma. arXiv:2610.35819 Sec. 10, remark (2)

If every multiset of size 8n - 7 over (ZMod n)^3 has an n-element zero-sum submultiset for all even n ≥ 6 not a power of 2, then every multiset of size 41 over (ZMod 6)^3 has a 6-element zero-sum submultiset.
-/

/-- The general rank-three Harborth bound equality implies the n = 6 case. -/
theorem harborth_bound_equality_rank_three_implies_six (h : ∀ (n : ℕ), 6 ≤ n → Even n → ¬ n.isPowerOfTwo → ∀ (S : Multiset (Fin 3 → ZMod n)), S.card = 8 * n - 7 → ∃ T : Multiset (Fin 3 → ZMod n), T ≤ S ∧ T.card = n ∧ T.sum = 0) : ∀ (S : Multiset (Fin 3 → ZMod 6)), S.card = 41 → ∃ T : Multiset (Fin 3 → ZMod 6), T ≤ S ∧ T.card = 6 ∧ T.sum = 0 := fun S hS => h 6 (by decide) (by decide) (by decide) S hS
