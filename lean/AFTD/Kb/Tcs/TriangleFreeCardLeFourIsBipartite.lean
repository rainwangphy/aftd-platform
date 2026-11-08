import AFTD.Prelude
import AFTD.Kb.Tcs.Order

/-!
# triangle_free_card_le_four_isBipartite

Topic: graphs   Node: b5eb1b16ea71

Provenance: helper lemma. step towards triangle_free_subcubic_card_le_four_partition

Every finite simple graph on at most 4 vertices that is triangle-free is bipartite (2-colorable).
-/

/-- Every finite simple graph on at most 4 vertices that is triangle-free is bipartite. -/
theorem triangle_free_card_le_four_isBipartite {V : Type*} [Fintype V]
    (G : SimpleGraph V) (htf : G.CliqueFree 3) (hcard : Fintype.card V ≤ 4) :
    G.IsBipartite := by
  classical
  -- In a triangle-free graph, three pairwise adjacent vertices are impossible.
  have no3 : ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c → False := by
    intro a b c hab hac hbc
    exact htf {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  by_cases hex : ∃ v : V, ∃ u w : V, G.Adj v u ∧ G.Adj v w ∧ u ≠ w
  · -- Case 1: some vertex `v` has two distinct neighbours `u`, `w`.
    -- Partition the vertices into `Nv = N(v)` and its complement `T`.
    -- `Nv` is independent (triangle-freeness) and `T` is independent because it has at most
    -- `4 - 2 = 2` elements and contains `v`, which is adjacent to nothing in `T`.
    obtain ⟨v, u, w, hvu, hvw, huw⟩ := hex
    set Nv : Finset V := G.neighborFinset v with hNv
    set T : Finset V := Finset.univ \ Nv with hT
    have hNvmem : ∀ x : V, x ∈ Nv ↔ G.Adj v x := by
      intro x; rw [hNv, SimpleGraph.mem_neighborFinset]
    have hTmem : ∀ x : V, x ∈ T ↔ ¬ G.Adj v x := by
      intro x
      rw [hT, Finset.mem_sdiff, hNvmem]
      simp
    have hNvcard : 2 ≤ Nv.card := by
      have hsub : ({u, w} : Finset V) ⊆ Nv := by
        intro x hx
        rw [hNvmem]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hvu
        · exact hvw
      have h2 : ({u, w} : Finset V).card = 2 := by simp [huw]
      calc 2 = ({u, w} : Finset V).card := h2.symm
        _ ≤ Nv.card := Finset.card_le_card hsub
    have hTcard : T.card ≤ 2 := by
      have h1 : T.card = Fintype.card V - Nv.card := by
        rw [hT, Finset.card_sdiff]; simp
      omega
    have hvT : v ∈ T := by rw [hTmem]; exact G.irrefl
    have hTindep : ∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b := by
      intro a ha b hb hab
      have hav : a ≠ v := by
        rintro rfl
        exact absurd hab ((hTmem b).mp hb)
      have hbv : b ≠ v := by
        rintro rfl
        exact absurd hab.symm ((hTmem a).mp ha)
      have h3 : ({v, a, b} : Finset V).card = 3 := by
        rw [Finset.card_eq_three]
        exact ⟨v, a, b, hav.symm, hbv.symm, hab.ne, rfl⟩
      have hsub : ({v, a, b} : Finset V) ⊆ T := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hvT
        · exact ha
        · exact hb
      have hc := Finset.card_le_card hsub
      omega
    refine SimpleGraph.IsBipartiteWith.isBipartite (s := (Nv : Set V)) (t := (T : Set V)) ⟨?_, ?_⟩
    · rw [hT]
      simp only [Finset.coe_sdiff, Finset.coe_univ]
      exact Set.disjoint_sdiff_right
    · intro a b hab
      by_cases ha : a ∈ Nv
      · by_cases hb : b ∈ Nv
        · exact absurd hab (no3 v a b ((hNvmem a).mp ha) ((hNvmem b).mp hb))
        · exact Or.inl ⟨by simpa using ha, by rw [hT]; simp [hb]⟩
      · by_cases hb : b ∈ Nv
        · exact Or.inr ⟨by rw [hT]; simp [ha], by simpa using hb⟩
        · exact absurd hab (hTindep a (by rw [hT]; simp [ha]) b (by rw [hT]; simp [hb]))
  · -- Case 2: every vertex has at most one neighbour, so `G` is a matching.
    -- Colour each vertex `x` with `0` if `x` is the smaller endpoint (in a fixed linear order
    -- induced by `Fintype.equivFin V`) of its edge, and with `1` otherwise.
    push Not at hex
    let e := Fintype.equivFin V
    have hinj : Function.Injective (fun v : V => (e v : ℕ)) := by
      intro a b hab
      exact e.injective (Fin.ext hab)
    let c : V → Fin 2 := fun v => if ∃ w, G.Adj v w ∧ (e v : ℕ) < (e w : ℕ) then 0 else 1
    refine ⟨SimpleGraph.Coloring.mk c ?_⟩
    intro a b hab
    have hab' : a ≠ b := hab.ne
    have hlt : (e a : ℕ) ≠ (e b : ℕ) := fun h => hab' (hinj h)
    rcases lt_or_gt_of_ne hlt with h | h
    · have hca : c a = 0 := by
        simp only [c]
        exact if_pos ⟨b, hab, h⟩
      have hcb : c b = 1 := by
        simp only [c]
        apply if_neg
        rintro ⟨x, hbx, hltx⟩
        have hxa : x = a := hex b x a hbx hab.symm
        rw [hxa] at hltx
        omega
      rw [hca, hcb]
      exact zero_ne_one
    · have hca : c a = 1 := by
        simp only [c]
        apply if_neg
        rintro ⟨x, hax, hltx⟩
        have hxb : x = b := hex a x b hax hab
        rw [hxb] at hltx
        omega
      have hcb : c b = 0 := by
        simp only [c]
        exact if_pos ⟨a, hab.symm, h⟩
      rw [hca, hcb]
      exact one_ne_zero
