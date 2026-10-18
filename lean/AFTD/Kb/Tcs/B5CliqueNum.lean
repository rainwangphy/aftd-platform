import AFTD.Prelude
import AFTD.Kb.Tcs.B5Graph
import AFTD.Kb.Tcs.B5GraphAdj
import AFTD.Kb.Tcs.G5Adj

/-!
# b5_cliqueNum

Topic: graphs   Node: de6c540247e9

Provenance: helper lemma. arXiv:2610.21388 (Stronger spectral bound for clique number), Sec. 2.2 (structural clique number of B_t) for t = 5; serves b5_clique_bound_iff

ω(B_5(n_0..n_4)) = n_4 + max(n_0 + n_1, n_1 + n_3, n_2 + n_3).
-/

/-- Cardinality of a full union of blocks: `Σ_{i ∈ T} n i`. -/
theorem b5_cliqueNum_card_sigma_univ (n : Fin 5 → ℕ) (T : Finset (Fin 5)) :
    (Finset.sigma T (fun i => (Finset.univ : Finset (Fin (n i))))).card = ∑ i ∈ T, n i := by
  rw [Finset.card_sigma]
  simp

/-- The union of blocks `{0,1,4}` has `n 0 + n 1 + n 4` vertices. -/
theorem b5_cliqueNum_card_014 (n : Fin 5 → ℕ) :
    (Finset.sigma {0,1,4} (fun i => (Finset.univ : Finset (Fin (n i))))).card
      = n 0 + n 1 + n 4 := by
  rw [b5_cliqueNum_card_sigma_univ]
  simp
  omega

/-- The union of blocks `{1,3,4}` has `n 1 + n 3 + n 4` vertices. -/
theorem b5_cliqueNum_card_134 (n : Fin 5 → ℕ) :
    (Finset.sigma {1,3,4} (fun i => (Finset.univ : Finset (Fin (n i))))).card
      = n 1 + n 3 + n 4 := by
  rw [b5_cliqueNum_card_sigma_univ]
  simp
  omega

/-- The union of blocks `{2,3,4}` has `n 2 + n 3 + n 4` vertices. -/
theorem b5_cliqueNum_card_234 (n : Fin 5 → ℕ) :
    (Finset.sigma {2,3,4} (fun i => (Finset.univ : Finset (Fin (n i))))).card
      = n 2 + n 3 + n 4 := by
  rw [b5_cliqueNum_card_sigma_univ]
  simp
  omega

/-- The cliques of `G₅` are contained in `{0,1,4}`, `{1,3,4}` or `{2,3,4}` (finite check). -/
theorem b5_cliqueNum_block_subset :
    ∀ A : Finset (Fin 5), (∀ i ∈ A, ∀ j ∈ A, i ≠ j → g5_adj i j) →
      (A ⊆ ({0,1,4} : Finset (Fin 5)) ∨ A ⊆ ({1,3,4} : Finset (Fin 5)) ∨
        A ⊆ ({2,3,4} : Finset (Fin 5))) := by
  decide

/-- The union of any set of pairwise adjacent blocks of `G₅` is a clique of `B_5`. -/
theorem b5_cliqueNum_sigma_univ_isClique (n : Fin 5 → ℕ) (T : Finset (Fin 5))
    (hT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → g5_adj i j) :
    (b5_graph n).IsClique ↑(Finset.sigma T (fun i => (Finset.univ : Finset (Fin (n i))))) := by
  intro x hx y hy hxy
  rw [b5_graph_adj]
  refine ⟨hxy, ?_⟩
  by_cases h : x.1 = y.1
  · exact Or.inl h
  · exact Or.inr (hT x.1 (Finset.mem_sigma.1 hx).1 y.1 (Finset.mem_sigma.1 hy).1 h)

theorem b5_cliqueNum (n : Fin 5 → ℕ) :
    (b5_graph n).cliqueNum = n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (b5_graph n).exists_isNClique_cliqueNum
    rw [← hs.card_eq]
    have hclique : ∀ i ∈ s.image (fun x => x.1), ∀ j ∈ s.image (fun x => x.1),
        i ≠ j → g5_adj i j := by
      intro i hi j hj hij
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hj
      have hxy : x ≠ y := by rintro rfl; exact hij rfl
      have h := (b5_graph_adj n x y).1 (hs.isClique hx hy hxy)
      rcases h.2 with h' | h'
      · exact absurd h' hij
      · exact h'
    rcases b5_cliqueNum_block_subset (s.image fun x => x.1) hclique with h014 | h134 | h234
    · have hsub : s ⊆ Finset.sigma {0,1,4} (fun i => (Finset.univ : Finset (Fin (n i)))) := by
        intro x hx
        exact Finset.mem_sigma.2 ⟨h014 (Finset.mem_image.2 ⟨x, hx, rfl⟩), Finset.mem_univ x.2⟩
      calc s.card ≤ _ := Finset.card_le_card hsub
        _ = n 0 + n 1 + n 4 := b5_cliqueNum_card_014 n
        _ ≤ n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) := by omega
    · have hsub : s ⊆ Finset.sigma {1,3,4} (fun i => (Finset.univ : Finset (Fin (n i)))) := by
        intro x hx
        exact Finset.mem_sigma.2 ⟨h134 (Finset.mem_image.2 ⟨x, hx, rfl⟩), Finset.mem_univ x.2⟩
      calc s.card ≤ _ := Finset.card_le_card hsub
        _ = n 1 + n 3 + n 4 := b5_cliqueNum_card_134 n
        _ ≤ n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) := by omega
    · have hsub : s ⊆ Finset.sigma {2,3,4} (fun i => (Finset.univ : Finset (Fin (n i)))) := by
        intro x hx
        exact Finset.mem_sigma.2 ⟨h234 (Finset.mem_image.2 ⟨x, hx, rfl⟩), Finset.mem_univ x.2⟩
      calc s.card ≤ _ := Finset.card_le_card hsub
        _ = n 2 + n 3 + n 4 := b5_cliqueNum_card_234 n
        _ ≤ n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) := by omega
  · have h1 := (b5_cliqueNum_sigma_univ_isClique n {0,1,4} (by decide)).card_le_cliqueNum
    have h2 := (b5_cliqueNum_sigma_univ_isClique n {1,3,4} (by decide)).card_le_cliqueNum
    have h3 := (b5_cliqueNum_sigma_univ_isClique n {2,3,4} (by decide)).card_le_cliqueNum
    rw [b5_cliqueNum_card_014 n] at h1
    rw [b5_cliqueNum_card_134 n] at h2
    rw [b5_cliqueNum_card_234 n] at h3
    omega
