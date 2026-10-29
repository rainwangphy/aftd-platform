import AFTD.Prelude

/-!
# erdos_ginzburg_ziv_constant

Topic: combinatorics   Node: 2971c2fda639

Provenance: formalization of a published result. Source: arXiv:2610.35819 Section 2

The Erdős–Ginzburg–Ziv constant of an additive commutative group G with respect to length n is the minimal integer k such that every multiset of size k over G contains a submultiset of size n summing to 0.
-/

/-- The Erdős–Ginzburg–Ziv constant s(G) of an abelian group with respect to length n. -/
noncomputable def erdos_ginzburg_ziv_constant (G : Type*) [AddCommGroup G] (n : ℕ) : ℕ := sInf { k : ℕ | ∀ S : Multiset G, S.card = k → ∃ T ≤ S, T.card = n ∧ T.sum = 0 }
