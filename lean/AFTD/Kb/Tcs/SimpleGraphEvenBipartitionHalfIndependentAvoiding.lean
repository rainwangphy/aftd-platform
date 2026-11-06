import AFTD.Prelude

/-!
# simple_graph_even_bipartition_half_independent_avoiding

Topic: graphs   Node: 7c81b1987cf0

Provenance: helper lemma. Elementary bipartition step in the paired-fork support route; scratch Lean checked.

If two disjoint independent vertex sets have a total of 2m vertices, then for any vertex one of them contains an independent m-set that avoids that vertex.
-/

theorem simple_graph_even_bipartition_half_independent_avoiding
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (m : ℕ) (z : V)
    (hdisj : Disjoint A B)
    (hA : G.IsIndepSet (A : Set V)) (hB : G.IsIndepSet (B : Set V))
    (hsize : A.card + B.card = 2 * m) :
    ∃ I : Finset V, m ≤ I.card ∧ z ∉ I ∧ G.IsIndepSet (I : Set V) := by
  classical
  by_cases hmA : m ≤ A.card
  · by_cases hzA : z ∈ A
    · by_cases hbig : m < A.card
      · refine ⟨A.erase z, ?_, by simp, ?_⟩
        · rw [Finset.card_erase_of_mem hzA]
          omega
        · exact hA.mono (by
            intro x hx
            exact (Finset.mem_erase.mp hx).2)
      · have hzB : z ∉ B := by
          intro hzB
          exact (Finset.disjoint_left.mp hdisj) hzA hzB
        exact ⟨B, by omega, hzB, hB⟩
    · exact ⟨A, hmA, hzA, hA⟩
  · refine ⟨B.erase z, ?_, by simp, ?_⟩
    · by_cases hzB : z ∈ B
      · rw [Finset.card_erase_of_mem hzB]
        omega
      · rw [Finset.erase_eq_of_notMem hzB]
        omega
    · exact hB.mono (by
        intro x hx
        exact (Finset.mem_erase.mp hx).2)
