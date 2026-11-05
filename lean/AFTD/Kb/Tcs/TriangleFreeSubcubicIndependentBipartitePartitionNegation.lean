import AFTD.Prelude

/-!
# triangle_free_subcubic_independent_bipartite_partition_negation

Topic: graphs   Node: 29c48b0b4b23

Provenance: formalization of a published result. Source: scout/2611-05178-weighted-max-cut-in-subcubic-graphs.md:1025

Refutation of Open Problem OP-1086: there exists a finite simple graph with maximum degree at most 3 that is triangle-free (contains no 3-clique) admitting no partition of its vertex set into an independent set L and complement R = Lᶜ such that G[R] is bipartite and for every connected component C of G[R] and every vertex v in L, the induced subgraph on V(C) ∪ {v} is bipartite.
-/

abbrev triangle_free_subcubic_independent_bipartite_partition_negation_graph :
    SimpleGraph (Fin 8) where
  Adj i j := j = i + 1 ∨ i = j + 1 ∨ j = i + 4 ∨ i = j + 4
  symm := ⟨fun i j h => by tauto⟩
  loopless := ⟨fun i h => by fin_cases i <;> exact absurd h (by decide)⟩

abbrev triangle_free_subcubic_independent_bipartite_partition_negation_cyc
    (i : Fin 8) (k : Fin 5) : Fin 8 := i + Fin.castLE (by omega) k

abbrev triangle_free_subcubic_independent_bipartite_partition_negation_rot
    (i : Fin 8) (k₀ k : Fin 5) : Fin 8 :=
  triangle_free_subcubic_independent_bipartite_partition_negation_cyc i (k₀ + k)

private lemma triangle_free_subcubic_independent_bipartite_partition_negation_cycle5
    {V : Type*} {G : SimpleGraph V} {S : Set V} (f : Fin 5 → V)
    (hmem : ∀ k : Fin 5, f k ∈ S) (hedge : ∀ k : Fin 5, G.Adj (f k) (f (k + 1))) :
    ¬ (G.induce S).IsBipartite := by
  rintro ⟨c⟩
  let a : Fin 5 → Fin 2 := fun k => c ⟨f k, hmem k⟩
  have hne : ∀ k : Fin 5, a k ≠ a (k + 1) := by
    intro k
    have h : (G.induce S).Adj ⟨f k, hmem k⟩ ⟨f (k + 1), hmem (k + 1)⟩ := by
      rw [SimpleGraph.induce_adj]; exact hedge k
    have h2 := c.map_rel h
    simpa [a] using h2
  have hval : ∀ k : Fin 5, (a k).val + (a (k + 1)).val = 1 := by
    intro k
    have h1 : (a k).val < 2 := (a k).isLt
    have h2 : (a (k + 1)).val < 2 := (a (k + 1)).isLt
    have h3 : (a k).val ≠ (a (k + 1)).val := by
      intro hh; exact hne k (Fin.ext hh)
    omega
  have h0 := hval 0
  have h1 := hval 1
  have h2 := hval 2
  have h3 := hval 3
  have h4 := hval 4
  simp only [show (0 : Fin 5) + 1 = 1 from rfl, show (1 : Fin 5) + 1 = 2 from rfl,
    show (2 : Fin 5) + 1 = 3 from rfl, show (3 : Fin 5) + 1 = 4 from rfl,
    show (4 : Fin 5) + 1 = 0 from rfl] at h0 h1 h2 h3 h4
  omega

/-- Refutation of Question 5.3 of arXiv:2611.05178 (OP-1086): there exists a finite triangle-free subcubic simple graph admitting no independent-bipartite component partition. -/
theorem triangle_free_subcubic_independent_bipartite_partition_negation :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.maxDegree ≤ 3 ∧
      G.CliqueFree 3 ∧
      ¬ ∃ L : Finset V,
        G.induce (L : Set V) = ⊥ ∧
        (G.induce (Lᶜ : Set V)).IsBipartite ∧
        ∀ C : (G.induce (Lᶜ : Set V)).ConnectedComponent,
          ∀ v ∈ L, (G.induce (Subtype.val '' (C : Set ↑(Lᶜ : Set V)) ∪ {v})).IsBipartite := by
  have hcyc_adj : ∀ (i : Fin 8) (k : Fin 5),
      triangle_free_subcubic_independent_bipartite_partition_negation_graph.Adj
        (triangle_free_subcubic_independent_bipartite_partition_negation_cyc i k)
        (triangle_free_subcubic_independent_bipartite_partition_negation_cyc i (k + 1)) := by
    decide
  have hrot_adj : ∀ (i : Fin 8) (k₀ : Fin 5) (k : Fin 5),
      triangle_free_subcubic_independent_bipartite_partition_negation_graph.Adj
        (triangle_free_subcubic_independent_bipartite_partition_negation_rot i k₀ k)
        (triangle_free_subcubic_independent_bipartite_partition_negation_rot i k₀ (k + 1)) := by
    intro i k₀ k
    have h : k₀ + (k + 1) = (k₀ + k) + 1 := by rw [add_assoc]
    rw [triangle_free_subcubic_independent_bipartite_partition_negation_rot,
      triangle_free_subcubic_independent_bipartite_partition_negation_rot, h]
    exact hcyc_adj i (k₀ + k)
  have hno_triangle : ∀ x y z : Fin 8,
      ¬ (triangle_free_subcubic_independent_bipartite_partition_negation_graph.Adj x y ∧
        triangle_free_subcubic_independent_bipartite_partition_negation_graph.Adj x z ∧
        triangle_free_subcubic_independent_bipartite_partition_negation_graph.Adj y z) := by
    decide
  have hkey : ∀ (L : Finset (Fin 8)),
      (∀ x ∈ L, ∀ y ∈ L,
        ¬ triangle_free_subcubic_independent_bipartite_partition_negation_graph.Adj x y) →
      (∃ i : Fin 8, ∀ k : Fin 5,
        triangle_free_subcubic_independent_bipartite_partition_negation_cyc i k ∉ L) ∨
      (∃ (i : Fin 8) (k₀ : Fin 5),
        triangle_free_subcubic_independent_bipartite_partition_negation_cyc i k₀ ∈ L ∧
        ∀ k' : Fin 5, k' ≠ 0 →
          triangle_free_subcubic_independent_bipartite_partition_negation_rot i k₀ k' ∉ L) := by
    decide
  refine ⟨Fin 8, inferInstance, inferInstance,
    triangle_free_subcubic_independent_bipartite_partition_negation_graph, inferInstance, ?_, ?_, ?_⟩
  · decide
  · intro t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
    exact hno_triangle x y z
      ⟨hcl (by simp) (by simp) hxy, hcl (by simp) (by simp) hxz, hcl (by simp) (by simp) hyz⟩
  · rintro ⟨L, hind, hbip, hcomp⟩
    have hL : ∀ x ∈ L, ∀ y ∈ L,
        ¬ triangle_free_subcubic_independent_bipartite_partition_negation_graph.Adj x y := by
      intro x hx y hy hxy
      have h1 : (triangle_free_subcubic_independent_bipartite_partition_negation_graph.induce
          (L : Set (Fin 8))).Adj ⟨x, by simpa using hx⟩ ⟨y, by simpa using hy⟩ := by
        rw [SimpleGraph.induce_adj]; exact hxy
      rw [hind] at h1
      simp at h1
    rcases hkey L hL with ⟨i, hi⟩ | ⟨i, k₀, hmem0, hrest⟩
    · refine (triangle_free_subcubic_independent_bipartite_partition_negation_cycle5
        (G := triangle_free_subcubic_independent_bipartite_partition_negation_graph)
        (S := (↑L : Set (Fin 8))ᶜ)
        (f := fun k => triangle_free_subcubic_independent_bipartite_partition_negation_cyc i k) ?_ ?_) hbip
      · intro k
        simpa using hi k
      · intro k
        exact hcyc_adj i k
    · have hRm : ∀ k' : Fin 5, k' ≠ 0 →
          triangle_free_subcubic_independent_bipartite_partition_negation_rot i k₀ k' ∈
            (↑L : Set (Fin 8))ᶜ := by
        intro k' hk'
        simpa using hrest k' hk'
      let p1 : ↥((↑L : Set (Fin 8))ᶜ) :=
        ⟨triangle_free_subcubic_independent_bipartite_partition_negation_rot i k₀ 1, hRm 1 (by decide)⟩
      let p2 : ↥((↑L : Set (Fin 8))ᶜ) :=
        ⟨triangle_free_subcubic_independent_bipartite_partition_negation_rot i k₀ 2, hRm 2 (by decide)⟩
      let p3 : ↥((↑L : Set (Fin 8))ᶜ) :=
        ⟨triangle_free_subcubic_independent_bipartite_partition_negation_rot i k₀ 3, hRm 3 (by decide)⟩
      let p4 : ↥((↑L : Set (Fin 8))ᶜ) :=
        ⟨triangle_free_subcubic_independent_bipartite_partition_negation_rot i k₀ 4, hRm 4 (by decide)⟩
      let C := (triangle_free_subcubic_independent_bipartite_partition_negation_graph.induce
        (↑L : Set (Fin 8))ᶜ).connectedComponentMk p1
      have h12 : (triangle_free_subcubic_independent_bipartite_partition_negation_graph.induce
          (↑L : Set (Fin 8))ᶜ).Adj p1 p2 := by
        rw [SimpleGraph.induce_adj]; exact hrot_adj i k₀ 1
      have h23 : (triangle_free_subcubic_independent_bipartite_partition_negation_graph.induce
          (↑L : Set (Fin 8))ᶜ).Adj p2 p3 := by
        rw [SimpleGraph.induce_adj]; exact hrot_adj i k₀ 2
      have h34 : (triangle_free_subcubic_independent_bipartite_partition_negation_graph.induce
          (↑L : Set (Fin 8))ᶜ).Adj p3 p4 := by
        rw [SimpleGraph.induce_adj]; exact hrot_adj i k₀ 3
      have h1C : p1 ∈ (C : Set ↥((↑L : Set (Fin 8))ᶜ)) := by
        change p1 ∈ C.supp
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      have h2C : p2 ∈ (C : Set ↥((↑L : Set (Fin 8))ᶜ)) :=
        (SimpleGraph.ConnectedComponent.mem_supp_congr_adj
          (G := triangle_free_subcubic_independent_bipartite_partition_negation_graph.induce
            (↑L : Set (Fin 8))ᶜ) C h12).mp h1C
      have h3C : p3 ∈ (C : Set ↥((↑L : Set (Fin 8))ᶜ)) :=
        (SimpleGraph.ConnectedComponent.mem_supp_congr_adj
          (G := triangle_free_subcubic_independent_bipartite_partition_negation_graph.induce
            (↑L : Set (Fin 8))ᶜ) C h23).mp h2C
      have h4C : p4 ∈ (C : Set ↥((↑L : Set (Fin 8))ᶜ)) :=
        (SimpleGraph.ConnectedComponent.mem_supp_congr_adj
          (G := triangle_free_subcubic_independent_bipartite_partition_negation_graph.induce
            (↑L : Set (Fin 8))ᶜ) C h34).mp h3C
      have hbipC := hcomp C
        (triangle_free_subcubic_independent_bipartite_partition_negation_cyc i k₀) hmem0
      refine (triangle_free_subcubic_independent_bipartite_partition_negation_cycle5
        (G := triangle_free_subcubic_independent_bipartite_partition_negation_graph)
        (S := Subtype.val '' (C : Set ↥((↑L : Set (Fin 8))ᶜ)) ∪
          {triangle_free_subcubic_independent_bipartite_partition_negation_cyc i k₀})
        (f := fun k => triangle_free_subcubic_independent_bipartite_partition_negation_rot i k₀ k) ?_ ?_) hbipC
      · intro k
        by_cases hk : k = 0
        · subst hk
          right
          simp [triangle_free_subcubic_independent_bipartite_partition_negation_rot]
        · left
          fin_cases k
          · exact absurd rfl hk
          · exact ⟨p1, h1C, rfl⟩
          · exact ⟨p2, h2C, rfl⟩
          · exact ⟨p3, h3C, rfl⟩
          · exact ⟨p4, h4C, rfl⟩
      · intro k
        exact hrot_adj i k₀ k
