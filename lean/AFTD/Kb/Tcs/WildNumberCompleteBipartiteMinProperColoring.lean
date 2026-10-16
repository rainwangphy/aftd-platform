import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfIsColorConnecting
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# wild_number_complete_bipartite_min_proper_coloring

Topic: graphs   Node: 8b1f07e162f8

Provenance: formalization of a published result. Source: arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Theorem 4.2. The Lean takes proper colourings with n colours (Fin n); since χ'(K_{m,n}) = Δ = n, these are exactly the minimum proper colourings of the paper.

Let 2 ≤ m ≤ n. For every proper edge colouring of the complete bipartite graph K_{m,n} with n colours (these are exactly its minimum proper edge colourings, since its chromatic index is its maximum degree n), the wild number is n.
-/

theorem wild_kmn_adj (m n : ℕ) (a : Fin m) (b : Fin n) :
    s(Sum.inl a, Sum.inr b) ∈ (completeBipartiteGraph (Fin m) (Fin n)).edgeSet := by
  simp

theorem wild_kmn_same_color_eq (m n : ℕ)
    (c : (completeBipartiteGraph (Fin m) (Fin n)).lineGraph.Coloring (Fin n))
    (a : Fin m) (b b' : Fin n)
    (h : c ⟨s(Sum.inl a, Sum.inr b), wild_kmn_adj m n a b⟩ =
      c ⟨s(Sum.inl a, Sum.inr b'), wild_kmn_adj m n a b'⟩) : b = b' := by
  by_contra hne
  apply c.valid _ h
  refine ⟨fun h' => hne ?_, ⟨Sum.inl a, by simp, by simp⟩⟩
  have := congrArg Subtype.val h'
  simpa using this

theorem wild_kmn_sees_all_colors (m n : ℕ)
    (c : (completeBipartiteGraph (Fin m) (Fin n)).lineGraph.Coloring (Fin n))
    (a : Fin m) (col : Fin n) :
    ∃ b : Fin n, c ⟨s(Sum.inl a, Sum.inr b), wild_kmn_adj m n a b⟩ = col := by
  have hinj : Function.Injective fun b : Fin n => c ⟨s(Sum.inl a, Sum.inr b), wild_kmn_adj m n a b⟩ :=
    fun b b' h => wild_kmn_same_color_eq m n c a b b' h
  exact (Finite.injective_iff_surjective.1 hinj) col

theorem wild_kmn_edge_cases (m n : ℕ) (f : Sym2 (Fin m ⊕ Fin n))
    (hf : f ∈ (completeBipartiteGraph (Fin m) (Fin n)).edgeSet) :
    ∃ a b, f = s(Sum.inl a, Sum.inr b) := by
  induction f using Sym2.ind with
  | h x y =>
    rcases x with a | b <;> rcases y with a' | b'
    · simp at hf
    · exact ⟨a, b', rfl⟩
    · exact ⟨a', b, Sym2.eq_swap⟩
    · simp at hf

theorem wild_number_complete_bipartite_min_proper_coloring (m n : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n)
    (c : (completeBipartiteGraph (Fin m) (Fin n)).lineGraph.Coloring (Fin n)) :
    simple_graph_wild_number (completeBipartiteGraph (Fin m) (Fin n)) c = n := by
  classical
  have a0 : Fin m := ⟨0, by omega⟩
  -- the star at a left vertex is colour-connecting
  let W0 : Finset (Sym2 (Fin m ⊕ Fin n)) :=
    Finset.univ.image fun b : Fin n => s(Sum.inl a0, Sum.inr b)
  have hW0card : W0.card = n := by
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro b b' h
    simpa using h
  have hW0 : simple_graph_is_color_connecting (completeBipartiteGraph (Fin m) (Fin n)) c ↑W0 := by
    refine ⟨?_, fun e => ?_⟩
    · intro f hf
      simp only [W0, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hf
      obtain ⟨b, rfl⟩ := hf
      exact wild_kmn_adj m n a0 b
    · rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨Sum.inl a0, fun v => ?_⟩
      have hr : ∀ b : Fin n, (SimpleGraph.fromEdgeSet ({f | ∃ hf : f ∈ (completeBipartiteGraph (Fin m) (Fin n)).edgeSet, c ⟨f, hf⟩ = c e} ∪
          ↑W0)).Reachable (Sum.inl a0) (Sum.inr b) := by
        intro b
        apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨Or.inr ?_, by simp⟩
        simp [W0]
      rcases v with a | b
      · obtain ⟨b, hb⟩ := wild_kmn_sees_all_colors m n c a (c e)
        refine (hr b).trans (SimpleGraph.Adj.reachable ?_)
        rw [SimpleGraph.fromEdgeSet_adj, Sym2.eq_swap]
        exact ⟨Or.inl ⟨wild_kmn_adj m n a b, hb⟩, by simp⟩
      · exact hr b
  -- every colour-connecting set has at least n edges
  have hlow : ∀ W : Finset (Sym2 (Fin m ⊕ Fin n)), simple_graph_is_color_connecting (completeBipartiteGraph (Fin m) (Fin n)) c ↑W →
      n ≤ W.card := by
    intro W hW
    -- the colour class of an edge e has at most m edges
    have hclass : ∀ e : (completeBipartiteGraph (Fin m) (Fin n)).edgeSet, ∃ CF : Finset (Sym2 (Fin m ⊕ Fin n)), CF.card ≤ m ∧
        {f | ∃ hf : f ∈ (completeBipartiteGraph (Fin m) (Fin n)).edgeSet, c ⟨f, hf⟩ = c e} ⊆ ↑CF := by
      intro e
      choose g hg using fun a => wild_kmn_sees_all_colors m n c a (c e)
      refine ⟨Finset.univ.image fun a => s(Sum.inl a, Sum.inr (g a)), ?_, ?_⟩
      · exact Finset.card_image_le.trans (by simp)
      · rintro f ⟨hf, hfc⟩
        obtain ⟨a, b, rfl⟩ := wild_kmn_edge_cases m n f hf
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
        refine ⟨a, ?_⟩
        have : g a = b := wild_kmn_same_color_eq m n c a (g a) b ((hg a).trans hfc.symm)
        rw [this]
    have hcount : ∀ e : (completeBipartiteGraph (Fin m) (Fin n)).edgeSet, ∀ R : Finset (Sym2 (Fin m ⊕ Fin n)),
        {f | ∃ hf : f ∈ (completeBipartiteGraph (Fin m) (Fin n)).edgeSet, c ⟨f, hf⟩ = c e} ∪ ↑W ⊆ ↑R → m + n ≤ R.card + 1 := by
      intro e R hR
      have hc := (hW.2 e).card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hc
      have : Nat.card (SimpleGraph.fromEdgeSet ({f | ∃ hf : f ∈ (completeBipartiteGraph (Fin m) (Fin n)).edgeSet, c ⟨f, hf⟩ = c e} ∪
          ↑W)).edgeSet ≤ R.card := by
        rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
        apply Nat.card_mono (Finset.finite_toSet R)
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact Set.sdiff_subset.trans hR
      omega
    by_cases hne : W.Nonempty
    · obtain ⟨w, hw⟩ := hne
      have hwE : w ∈ (completeBipartiteGraph (Fin m) (Fin n)).edgeSet := hW.1 hw
      obtain ⟨CF, hCF, hsub⟩ := hclass ⟨w, hwE⟩
      have hwC : w ∈ CF := hsub ⟨hwE, rfl⟩
      have := hcount ⟨w, hwE⟩ (CF ∪ W.erase w) (by
        intro f hf
        rcases hf with hf | hf
        · exact Finset.mem_coe.2 (Finset.mem_union_left _ (hsub hf))
        · by_cases hfw : f = w
          · subst hfw; exact Finset.mem_coe.2 (Finset.mem_union_left _ hwC)
          · exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hfw, hf⟩)))
      have h1 := Finset.card_union_le CF (W.erase w)
      have h2 := Finset.card_erase_of_mem hw
      have h3 := Finset.card_pos.2 ⟨w, hw⟩
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      obtain ⟨CF, hCF, hsub⟩ := hclass ⟨_, wild_kmn_adj m n a0 ⟨0, by omega⟩⟩
      have := hcount ⟨_, wild_kmn_adj m n a0 ⟨0, by omega⟩⟩ CF (by simpa using hsub)
      omega
  unfold simple_graph_wild_number
  apply le_antisymm
  · have h := Nat.sInf_le (show W0.card ∈ {k | ∃ W : Finset (Sym2 (Fin m ⊕ Fin n)), W.card = k ∧
        simple_graph_is_color_connecting (completeBipartiteGraph (Fin m) (Fin n)) c ↑W} from
        ⟨W0, rfl, hW0⟩)
    rw [hW0card] at h
    exact h
  · exact le_csInf ⟨n, W0, hW0card, hW0⟩ fun k ⟨W, hk, hW⟩ => by rw [← hk]; exact hlow W hW
