import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_both_cuts_ge_ceil_div_six_of_high_indegree

Topic: graphs   Node: 15bed73668d9

Provenance: helper lemma. arXiv:2610.21381, proof of Theorem 1.4 (Section 5), the case d⁻(z) ≥ m/3 + 1

Case 1 of the proof of Theorem 1.4: in a loopless digraph with m arcs, if a vertex z has in-degree at least m/3 + 1 and some set A₀ ∋ z has e(A₀, V∖A₀) ≥ m/6, then some set A has e(A, V∖A) ≥ ⌈m/6⌉ and e(V∖A, A) ≥ ⌈m/6⌉ (keep z and the tails of ⌈m/6⌉ arcs leaving A₀).
-/

theorem digraph_both_cuts_ge_ceil_div_six_of_high_indegree {V : Type*} [Fintype V]
    [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (hloop : ∀ v, ¬ G.Adj v v)
    (z : V) (A₀ : Finset V) (hz : z ∈ A₀)
    (hcut : (digraph_edge_count G : ℚ) / 6 ≤ digraph_cut_count G A₀ A₀ᶜ)
    (hin : (digraph_edge_count G : ℚ) / 3 + 1 ≤
      (Finset.univ.filter fun u => G.Adj u z).card) :
    ∃ A : Finset V, ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G A Aᶜ ∧
      ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G Aᶜ A := by
  set m := digraph_edge_count G
  set k := ⌈(m : ℚ) / 6⌉₊
  set S := (A₀ ×ˢ A₀ᶜ).filter fun p => G.Adj p.1 p.2 with hS
  have hkS : k ≤ S.card := Nat.ceil_le.2 hcut
  obtain ⟨C, hCS, hCk⟩ := Finset.exists_subset_card_eq hkS
  set T := C.image Prod.fst
  have hTA₀ : T ⊆ A₀ := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
    have := hCS hp
    simp only [hS, Finset.mem_filter, Finset.mem_product] at this
    exact this.1.1
  refine ⟨insert z T, ?_, ?_⟩
  · rw [← hCk]
    unfold digraph_cut_count
    apply Finset.card_le_card
    intro p hp
    have hp' := hCS hp
    simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_compl] at hp'
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl, Finset.mem_insert]
    refine ⟨⟨Or.inr (Finset.mem_image_of_mem _ hp), ?_⟩, hp'.2⟩
    rintro (h | h)
    · exact hp'.1.2 (h ▸ hz)
    · exact hp'.1.2 (hTA₀ h)
  · set I := Finset.univ.filter fun u => G.Adj u z
    have hk : (k : ℚ) < m / 6 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2k : 2 * k ≤ I.card := by
      have : ((2 * k : ℕ) : ℚ) < (I.card : ℚ) + 1 := by push_cast; linarith
      exact Nat.lt_add_one_iff.1 (by exact_mod_cast this)
    have hIT : I.card ≤ (I \ insert z T).card + k := by
      have h1 : I ⊆ (I \ insert z T) ∪ T := by
        intro u hu
        by_cases huT : u ∈ T
        · exact Finset.mem_union_right _ huT
        · refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hu, ?_⟩)
          rw [Finset.mem_insert]
          rintro (rfl | h)
          · exact hloop u (Finset.mem_filter.1 hu).2
          · exact huT h
      calc I.card ≤ ((I \ insert z T) ∪ T).card := Finset.card_le_card h1
        _ ≤ (I \ insert z T).card + T.card := Finset.card_union_le _ _
        _ ≤ (I \ insert z T).card + k := by
          have : T.card ≤ C.card := Finset.card_image_le
          omega
    have hD : (I \ insert z T).card ≤ digraph_cut_count G (insert z T)ᶜ (insert z T) := by
      unfold digraph_cut_count
      rw [← Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1 :
        Function.Injective fun u : V => (u, z))]
      apply Finset.card_le_card
      intro p hp
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hp
      rw [Finset.mem_sdiff] at hu
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl,
        Finset.mem_insert_self, and_true]
      exact ⟨hu.2, (Finset.mem_filter.1 hu.1).2⟩
    omega
