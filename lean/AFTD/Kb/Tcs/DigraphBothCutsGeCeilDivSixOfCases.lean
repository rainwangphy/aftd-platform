import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_both_cuts_ge_ceil_div_six_of_cases

Topic: graphs   Node: 1be7168768a9

Provenance: helper lemma. arXiv:2610.21381 Section 5 lines 1506-1524

If a finite digraph G admits a vertex subset A with both directed cut counts e(A, Aᶜ) and e(Aᶜ, A) at least ⌈m/6⌉ whenever some vertex has in-degree at least m/3 + 1, and also whenever every vertex has in-degree strictly below m/3 + 1, then there exists a vertex bipartition V = A ⊔ B with e(A, B) ≥ ⌈m/6⌉ and e(B, A) ≥ ⌈m/6⌉.
-/

/-- Case reduction for Theorem 1.4: if a digraph admits ceil(m/6) cuts in both directions under high in-degree and under low in-degree, then it admits such a bipartition unconditionally. -/
theorem digraph_both_cuts_ge_ceil_div_six_of_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj]
    (h_high : (∃ z : V, (digraph_edge_count G : ℚ) / 3 + 1 ≤
      ((Finset.univ.filter fun u => G.Adj u z).card : ℚ)) →
      ∃ A : Finset V, ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G A Aᶜ ∧
        ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G Aᶜ A)
    (h_low : (∀ v : V, ((Finset.univ.filter fun u => G.Adj u v).card : ℚ) <
      (digraph_edge_count G : ℚ) / 3 + 1) →
      ∃ A : Finset V, ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G A Aᶜ ∧
        ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G Aᶜ A) :
    ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = Finset.univ ∧
      ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G A B ∧
      ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G B A := by
  by_cases h : ∃ z : V, (digraph_edge_count G : ℚ) / 3 + 1 ≤
      ((Finset.univ.filter fun u => G.Adj u z).card : ℚ)
  · rcases h_high h with ⟨A, hA, hA'⟩
    exact ⟨A, Aᶜ, by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact (Finset.mem_compl.mp hb) ha, Finset.union_compl A, hA, hA'⟩
  · have hlow : ∀ v : V, ((Finset.univ.filter fun u => G.Adj u v).card : ℚ) <
        (digraph_edge_count G : ℚ) / 3 + 1 := by
      intro v
      exact not_le.mp (fun hle => h ⟨v, hle⟩)
    rcases h_low hlow with ⟨A, hA, hA'⟩
    exact ⟨A, Aᶜ, by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact (Finset.mem_compl.mp hb) ha, Finset.union_compl A, hA, hA'⟩
