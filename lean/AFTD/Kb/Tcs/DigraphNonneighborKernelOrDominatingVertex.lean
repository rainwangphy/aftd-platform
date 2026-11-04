import AFTD.Prelude

/-!
# digraph_nonneighbor_kernel_or_dominating_vertex

Topic: graphs   Node: a3ebec5c3a1a

Provenance: helper lemma. Proof of Theorem 3.4, step (1), in https://people.maths.ox.ac.uk/~scott/Papers/2kernels.pdf; only the kernel of the non-neighborhood is used, and no novelty is claimed.

Given an out-kernel K of the non-neighbors of a vertex v, either {v}∪K is a quasi-kernel or there is a distinct vertex w pointing to v whose in-neighbors all point to v too.
-/

theorem digraph_nonneighbor_kernel_or_dominating_vertex
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (v : α) (K : Finset α)
    (hK : ∀ x ∈ K, x ≠ v ∧ ¬ D.Adj x v ∧ ¬ D.Adj v x)
    (hind : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → ¬ D.Adj x y)
    (hdom : ∀ x, x ≠ v → ¬ D.Adj x v → ¬ D.Adj v x →
      ∃ k ∈ K, k = x ∨ D.Adj k x) :
    ((∀ x ∈ insert v K, ∀ y ∈ insert v K, x ≠ y → ¬ D.Adj x y) ∧
      (∀ x, ∃ q ∈ insert v K,
        q = x ∨ D.Adj q x ∨ ∃ z, D.Adj q z ∧ D.Adj z x)) ∨
    ∃ w, w ≠ v ∧ D.Adj w v ∧ ∀ z, D.Adj z w → D.Adj z v := by
  classical
  by_cases hq : ∀ x, ∃ q ∈ insert v K,
      q = x ∨ D.Adj q x ∨ ∃ z, D.Adj q z ∧ D.Adj z x
  · left
    refine ⟨?_, hq⟩
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxv | hxK
    · subst x
      rcases Finset.mem_insert.mp hy with hyv | hyK
      · subst y
        exact (hxy rfl).elim
      · exact (hK y hyK).2.2
    · rcases Finset.mem_insert.mp hy with hyv | hyK
      · subst y
        exact (hK x hxK).2.1
      · exact hind x hxK y hyK hxy
  · right
    obtain ⟨w, hw⟩ := not_forall.mp hq
    have hne : w ≠ v := by
      intro h
      subst w
      apply hw
      exact ⟨v, by simp, Or.inl rfl⟩
    have hvw : ¬ D.Adj v w := by
      intro h
      apply hw
      exact ⟨v, by simp, Or.inr (Or.inl h)⟩
    have hwv : D.Adj w v := by
      by_contra h
      obtain ⟨k, hk, hkw⟩ := hdom w hne h hvw
      apply hw
      exact ⟨k, Finset.mem_insert_of_mem hk,
        hkw.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
    refine ⟨w, hne, hwv, ?_⟩
    intro z hzw
    by_contra hzv
    have hzneq : z ≠ v := by
      intro h
      subst z
      exact hvw hzw
    have hvz : ¬ D.Adj v z := by
      intro h
      apply hw
      exact ⟨v, by simp, Or.inr (Or.inr ⟨z, h, hzw⟩)⟩
    obtain ⟨k, hk, hkz⟩ := hdom z hzneq hzv hvz
    apply hw
    refine ⟨k, Finset.mem_insert_of_mem hk, ?_⟩
    rcases hkz with rfl | hkz
    · exact Or.inr (Or.inl hzw)
    · exact Or.inr (Or.inr ⟨z, hkz, hzw⟩)
