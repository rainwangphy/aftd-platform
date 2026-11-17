import AFTD.Prelude
import AFTD.Kb.Tcs.IsFactorizationCoarsening

/-!
# isFactorizationCoarsening_refl

Topic: combinatorics   Node: 9815df3e9ecc

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): sanity lemma for the factorization-poset definitions

Every multiset is a coarsening of itself (the partition into singletons).
-/

theorem isFactorizationCoarsening_refl (x : Multiset ℕ) : IsFactorizationCoarsening x x := by
  refine ⟨x.map (fun a => {a}), ?_, ?_, ?_⟩
  · simp
  · simp [Multiset.join]
  · simp
