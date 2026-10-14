import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberEqZeroOfCliqueFree

/-!
# simple_graph_triangle_cover_number_le_three_mul_packing_number

Topic: graphs   Node: 0e94eb51f077

Provenance: formalization of a published result. Source: The trivial bound ν(G) ≤ τ(G) ≤ 3ν(G), recalled in arXiv:2610.15539 (Tuza's conjecture under an edge-count condition), Sec. 1 (display after Conjecture 1.1); the bound Tuza's conjecture improves to 2ν.

Every finite graph satisfies τ(G) ≤ 3ν(G): the edges of a maximum family of edge-disjoint triangles meet every triangle.
-/

theorem simple_graph_triangle_cover_number_le_three_mul_packing_number {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) :
    simple_graph_triangle_cover_number G ≤ 3 * simple_graph_triangle_packing_number G := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · rw [simple_graph_triangle_cover_number_eq_zero_of_clique_free G (fun t ht => by
        have := ht.card_eq
        rw [Finset.eq_empty_of_isEmpty t, Finset.card_empty] at this
        omega)]
    exact Nat.zero_le _
  set P : Set ℕ := {n | ∃ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) ∧
    (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n} with hP
  have hbdd : BddAbove P := by
    refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
    rintro n ⟨T, -, -, rfl⟩
    exact Finset.card_le_univ T
  have hne : P.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  obtain ⟨T, hT, hTp, hTc⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ T' : Finset (Finset V), (∀ t ∈ T', G.IsNClique 3 t) →
      (T' : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) → T'.card ≤ T.card := by
    intro T' h1 h2
    rw [hTc]
    exact le_csSup hbdd ⟨T', h1, h2, rfl⟩
  -- three edges of each triangle
  have h3 : ∀ t ∈ T, ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ t = {x, y, z} := by
    intro t ht
    exact Finset.card_eq_three.1 (hT t ht).card_eq
  choose! fx fy fz hxy hxz hyz hxyz using h3
  set E : Finset V → Finset (Sym2 V) :=
    fun t => {s(fx t, fy t), s(fy t, fz t), s(fx t, fz t)} with hE
  set F := T.biUnion E with hF
  have hFcard : F.card ≤ 3 * T.card := by
    calc F.card ≤ ∑ t ∈ T, (E t).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ T, 3 := by
          apply Finset.sum_le_sum
          intro t _
          simp only [hE]
          exact (Finset.card_insert_le _ _).trans
            (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
      _ = 3 * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hFedge : ∀ e ∈ F, e ∈ G.edgeSet := by
    intro e he
    simp only [hF, Finset.mem_biUnion] at he
    obtain ⟨t, ht, he⟩ := he
    have hcl := (hT t ht).isClique
    have hsub : ∀ x ∈ ({fx t, fy t, fz t} : Finset V), x ∈ t := by
      intro x hx
      rw [← hxyz t ht] at hx
      exact hx
    have hx : fx t ∈ t := hsub _ (by simp)
    have hy : fy t ∈ t := hsub _ (by simp)
    have hz : fz t ∈ t := hsub _ (by simp)
    simp only [hE, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hcl hx hy (hxy t ht)
    · exact hcl hy hz (hyz t ht)
    · exact hcl hx hz (hxz t ht)
  -- every pair of distinct vertices of a packing triangle spans one of its three edges
  have hpair : ∀ s ∈ T, ∀ u ∈ s, ∀ w ∈ s, u ≠ w → s(u, w) ∈ E s := by
    intro s hs u hu w hw huw
    rw [hxyz s hs] at hu hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
    simp only [hE, Finset.mem_insert, Finset.mem_singleton]
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first
      | exact absurd rfl huw
      | simp [Sym2.eq_swap]
  have hcover : ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ F, ∀ x ∈ e, x ∈ t := by
    intro t ht
    -- some packing triangle shares two vertices with `t`
    have : ∃ s ∈ T, 2 ≤ (s ∩ t).card := by
      by_contra hno
      push_neg at hno
      have htT : t ∉ T := by
        intro htT
        have := hno t htT
        rw [Finset.inter_self, ht.card_eq] at this
        omega
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
        have := hno s hs
        exact ⟨by rw [Finset.inter_comm]; omega, by omega⟩
      have := hmax _ h1 h2
      rw [Finset.card_insert_of_notMem htT] at this
      omega
    obtain ⟨s, hs, hst⟩ := this
    obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.1 hst
    rw [Finset.mem_inter] at hu hw
    refine ⟨s(u, w), Finset.mem_biUnion.2 ⟨s, hs, hpair s hs u hu.1 w hw.1 huw⟩, ?_⟩
    intro x hx
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact hu.2
    · exact hw.2
  calc simple_graph_triangle_cover_number G ≤ F.card :=
        Nat.sInf_le ⟨F, hFedge, hcover, rfl⟩
    _ ≤ 3 * T.card := hFcard
    _ = 3 * simple_graph_triangle_packing_number G := by
        rw [hTc]; rfl
