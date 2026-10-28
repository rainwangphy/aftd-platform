import AFTD.Prelude
import AFTD.Kb.Tcs.CardSimpleGraph

/-!
# ncard_even_edge_graphs

Topic: combinatorics   Node: 30394ab24168

Provenance: helper lemma. arXiv:2610.35136, Sharp Bounds for Graph-Codes Avoiding Complete Bipartite Differences, Proposition 3.2

For every natural number n ≥ 2, the cardinality of the set of simple graphs on vertex set [n] having an even number of edges is 2^{n choose 2 - 1}.
-/

/-- Toggle the edge `e` in the graph `G`. -/
private def ncard_even_edge_graphs_flip {n : ℕ} (e : Sym2 (Fin n)) (G : SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (symmDiff G.edgeSet ({e} : Set (Sym2 (Fin n))))

/-- The edge set of the toggled graph is the symmetric difference of edge sets. -/
private theorem ncard_even_edge_graphs_flip_edgeSet {n : ℕ} (e : Sym2 (Fin n)) (he : ¬ e.IsDiag)
    (G : SimpleGraph (Fin n)) :
    (ncard_even_edge_graphs_flip e G).edgeSet = symmDiff G.edgeSet ({e} : Set (Sym2 (Fin n))) := by
  simp only [ncard_even_edge_graphs_flip, SimpleGraph.edgeSet_fromEdgeSet]
  ext x
  simp only [Set.mem_sdiff, Set.mem_symmDiff, Set.mem_singleton_iff, Sym2.mem_diagSet]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h
    refine ⟨h, ?_⟩
    rcases h with ⟨hxG, hxe⟩ | ⟨hxe, hxG⟩
    · exact G.not_isDiag_of_mem_edgeSet hxG
    · subst hxe; exact he

/-- Toggling the same non-loop edge twice is the identity. -/
private theorem ncard_even_edge_graphs_flip_involutive {n : ℕ} (e : Sym2 (Fin n))
    (he : ¬ e.IsDiag) (G : SimpleGraph (Fin n)) :
    ncard_even_edge_graphs_flip e (ncard_even_edge_graphs_flip e G) = G := by
  apply SimpleGraph.edgeSet_inj.mp
  rw [ncard_even_edge_graphs_flip_edgeSet e he (ncard_even_edge_graphs_flip e G),
    ncard_even_edge_graphs_flip_edgeSet e he G]
  exact symmDiff_symmDiff_cancel_right ({e} : Set (Sym2 (Fin n))) G.edgeSet

/-- Toggling a non-loop edge flips the parity of the number of edges. -/
private theorem ncard_even_edge_graphs_flip_ncard_even {n : ℕ} (e : Sym2 (Fin n))
    (he : ¬ e.IsDiag) (G : SimpleGraph (Fin n)) :
    Even (ncard_even_edge_graphs_flip e G).edgeSet.ncard ↔ ¬ Even G.edgeSet.ncard := by
  classical
  rw [ncard_even_edge_graphs_flip_edgeSet e he G]
  by_cases hmem : e ∈ G.edgeSet
  · have hsub : ({e} : Set (Sym2 (Fin n))) ⊆ G.edgeSet := Set.singleton_subset_iff.mpr hmem
    have hset : symmDiff G.edgeSet ({e} : Set (Sym2 (Fin n))) = G.edgeSet \ {e} := by
      rw [Set.symmDiff_def, Set.sdiff_eq_empty.mpr hsub, Set.union_empty]
    rw [hset, Set.ncard_sdiff hsub, Set.ncard_singleton]
    have hpos : 1 ≤ G.edgeSet.ncard := by
      have h0 : 0 < G.edgeSet.ncard := by
        rw [Set.ncard_pos]
        exact ⟨e, hmem⟩
      omega
    rw [Nat.even_sub hpos]
    simp
  · have hset : symmDiff G.edgeSet ({e} : Set (Sym2 (Fin n))) = insert e G.edgeSet := by
      ext x
      simp only [Set.mem_symmDiff, Set.mem_singleton_iff, Set.mem_insert_iff]
      constructor
      · rintro (⟨hx, -⟩ | ⟨rfl, -⟩)
        · exact Or.inr hx
        · exact Or.inl rfl
      · rintro (rfl | hx)
        · exact Or.inr ⟨rfl, hmem⟩
        · exact Or.inl ⟨hx, fun hxe => hmem (hxe ▸ hx)⟩
    rw [hset, Set.ncard_insert_of_notMem hmem, Nat.even_add_one]

/-- The parity of the number of edges equals the parity of the edge-set cardinality. -/
private theorem ncard_even_edge_graphs_even_iff {n : ℕ} (G : SimpleGraph (Fin n)) :
    (open Classical in Even G.edgeFinset.card ↔ Even G.edgeSet.ncard) := by
  classical
  rw [SimpleGraph.edgeFinset_card, Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- Toggling a non-loop edge flips the parity of the edge count. -/
private theorem ncard_even_edge_graphs_flip_even {n : ℕ} (e : Sym2 (Fin n))
    (he : ¬ e.IsDiag) (G : SimpleGraph (Fin n)) :
    (open Classical in
      Even (ncard_even_edge_graphs_flip e G).edgeFinset.card ↔ ¬ Even G.edgeFinset.card) := by
  rw [ncard_even_edge_graphs_even_iff, ncard_even_edge_graphs_even_iff,
    ncard_even_edge_graphs_flip_ncard_even e he G]

/-- Exactly half of all simple graphs on Fin n have an even number of edges for n ≥ 2. -/
theorem ncard_even_edge_graphs (n : ℕ) (hn : 2 ≤ n) :
    Set.ncard (open Classical in {G : SimpleGraph (Fin n) | Even G.edgeFinset.card}) = 2 ^ (n.choose 2 - 1) := by
  classical
  set e : Sym2 (Fin n) := s(⟨0, by omega⟩, ⟨1, by omega⟩)
  have he : ¬ e.IsDiag := by
    rw [Sym2.mk_isDiag_iff]
    intro h
    have h2 : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  set S : Set (SimpleGraph (Fin n)) := {G | Even G.edgeFinset.card} with hS
  have hcongr : S.ncard = Sᶜ.ncard := by
    refine Set.ncard_congr (fun G _ => ncard_even_edge_graphs_flip e G) ?_ ?_ ?_
    · intro G hG
      simp only [hS, Set.mem_ofPred_eq] at hG
      simp only [Set.mem_compl_iff, hS, Set.mem_ofPred_eq]
      exact fun h => (ncard_even_edge_graphs_flip_even e he G).mp h hG
    · intro G₁ G₂ _ _ h
      rw [← ncard_even_edge_graphs_flip_involutive e he G₁,
        ← ncard_even_edge_graphs_flip_involutive e he G₂, h]
    · intro G hG
      simp only [Set.mem_compl_iff, hS, Set.mem_ofPred_eq] at hG
      refine ⟨ncard_even_edge_graphs_flip e G, ?_,
        ncard_even_edge_graphs_flip_involutive e he G⟩
      simp only [hS, Set.mem_ofPred_eq]
      exact (ncard_even_edge_graphs_flip_even e he G).mpr hG
  have hsum : S.ncard + Sᶜ.ncard = 2 ^ n.choose 2 := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, card_simpleGraph,
      Fintype.card_fin]
  rw [← hcongr] at hsum
  have hk : 0 < n.choose 2 := Nat.choose_pos hn
  have hk1 : n.choose 2 - 1 + 1 = n.choose 2 := Nat.sub_one_add_one hk.ne'
  have h2 : 2 ^ n.choose 2 = 2 * 2 ^ (n.choose 2 - 1) := by
    conv_lhs => rw [← hk1]
    rw [pow_succ']
  have hh : 2 * S.ncard = 2 * 2 ^ (n.choose 2 - 1) := by
    rw [two_mul]; exact hsum.trans h2
  exact Nat.mul_left_cancel (by norm_num) hh
