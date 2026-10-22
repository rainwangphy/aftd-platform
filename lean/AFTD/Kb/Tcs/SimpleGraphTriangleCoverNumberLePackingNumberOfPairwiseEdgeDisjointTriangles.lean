import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_cover_number_le_packing_number_of_pairwise_edge_disjoint_triangles

Topic: graphs   Node: 126449b05f9d

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

If any two distinct triangles of a finite graph G share at most one vertex (equivalently, no edge lies in two triangles), then τ(G) ≤ ν(G), hence in particular τ(G) ≤ 2ν(G).
-/

/-- When distinct triangles of G share at most one vertex, τ(G) ≤ ν(G) (a strict strengthening of τ ≤ 2ν on that class). -/
theorem simple_graph_triangle_cover_number_le_packing_number_of_pairwise_edge_disjoint_triangles
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hdisj : ∀ s t : Finset V, G.IsNClique 3 s → G.IsNClique 3 t → s ≠ t →
      (s ∩ t).card ≤ 1) :
    simple_graph_triangle_cover_number G ≤ simple_graph_triangle_packing_number G := by
  classical
  -- the set of attainable packing sizes
  set P : Set ℕ := {n | ∃ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) ∧
    (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n} with hP
  have hbdd : BddAbove P := by
    refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
    rintro n ⟨T, -, -, rfl⟩
    exact Finset.card_le_univ T
  have hne : P.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  -- a maximum packing
  obtain ⟨T, hT, hTp, hTc⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ T' : Finset (Finset V), (∀ t ∈ T', G.IsNClique 3 t) →
      (T' : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) → T'.card ≤ T.card := by
    intro T' h1 h2
    rw [hTc]
    exact le_csSup hbdd ⟨T', h1, h2, rfl⟩
  -- key step: since triangles are pairwise edge-disjoint, a maximal packing contains every triangle
  have hmem : ∀ t : Finset V, G.IsNClique 3 t → t ∈ T := by
    intro t ht
    by_contra htT
    have h1 : ∀ s ∈ insert t T, G.IsNClique 3 s := by
      intro s hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact ht
      · exact hT s hs
    have h2 : ((insert t T : Finset (Finset V)) : Set (Finset V)).Pairwise
        (fun s t => (s ∩ t).card ≤ 1) := by
      rw [Finset.coe_insert]
      refine hTp.insert ?_
      intro s hs _
      have hst' : s ≠ t := fun h => htT (h ▸ hs)
      have h := hdisj s t (hT s hs) ht hst'
      exact ⟨by rw [Finset.inter_comm]; exact h, h⟩
    have := hmax _ h1 h2
    rw [Finset.card_insert_of_notMem htT] at this
    omega
  -- one edge through each triangle of the packing
  have h2 : ∀ p : {t : Finset V // t ∈ T}, ∃ x y : V, x ∈ p.1 ∧ y ∈ p.1 ∧ x ≠ y := by
    intro p
    obtain ⟨x, y, z, hxy, -, -, hx⟩ := Finset.card_eq_three.1 (hT p.1 p.2).card_eq
    exact ⟨x, y, hx ▸ by simp, hx ▸ by simp, hxy⟩
  choose fx fy hfx hfy hfxy using h2
  set F : Finset (Sym2 V) := T.attach.image (fun p : {t : Finset V // t ∈ T} => s(fx p, fy p)) with hF
  have hFcard : F.card ≤ T.card := by
    rw [hF]
    calc (T.attach.image (fun p : {t : Finset V // t ∈ T} => s(fx p, fy p))).card
        ≤ T.attach.card := Finset.card_image_le
      _ = T.card := Finset.card_attach
  have hFedge : ∀ e ∈ F, e ∈ G.edgeSet := by
    intro e he
    rw [hF] at he
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
    exact (hT p.1 p.2).isClique (hfx p) (hfy p) (hfxy p)
  have hcover : ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ F, ∀ x ∈ e, x ∈ t := by
    intro t ht
    have htT := hmem t ht
    refine ⟨s(fx ⟨t, htT⟩, fy ⟨t, htT⟩), ?_, ?_⟩
    · rw [hF]
      exact Finset.mem_image.2 ⟨⟨t, htT⟩, Finset.mem_attach _ _, rfl⟩
    · intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact hfx ⟨t, htT⟩
      · exact hfy ⟨t, htT⟩
  calc simple_graph_triangle_cover_number G ≤ F.card :=
        Nat.sInf_le ⟨F, hFedge, hcover, rfl⟩
    _ ≤ T.card := hFcard
    _ = simple_graph_triangle_packing_number G := hTc
