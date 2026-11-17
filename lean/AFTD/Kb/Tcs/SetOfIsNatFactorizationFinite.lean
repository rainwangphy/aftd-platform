import AFTD.Prelude
import AFTD.Kb.Tcs.IsNatFactorization
import AFTD.Kb.Tcs.OrderedFactorizationFinite

/-!
# setOf_isNatFactorization_finite

Topic: combinatorics   Node: c55c307ef930

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): sanity lemma for the factorization-poset definitions

Every natural number has only finitely many factorizations into integers greater than 1.
-/

theorem setOf_isNatFactorization_finite (n : ℕ) :
    {x : Multiset ℕ | IsNatFactorization n x}.Finite := by
  have := orderedFactorization_finite n
  apply (Set.finite_range
    (fun l : {l : List ℕ // (∀ a ∈ l, 1 < a) ∧ l.prod = n} => (l.1 : Multiset ℕ))).subset
  rintro x ⟨hx1, hx2⟩
  refine ⟨⟨x.toList, fun a ha => hx1 a (Multiset.mem_toList.mp ha), ?_⟩, ?_⟩
  · rw [← Multiset.prod_toList] at hx2; exact hx2
  · simp
