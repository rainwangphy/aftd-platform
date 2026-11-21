import AFTD.Prelude
import AFTD.Kb.Tcs.Op2037SubgraphFintype

/-!
# even_graph_four_odd_component_bounds_has_perfect_matching

Topic: graphs   Node: 4455cce66814

Provenance: helper lemma. OP-1957: matching-criterion assembly for the (5,7) example.

An even-order finite graph has a perfect matching if, after removing zero vertices, it has no odd component, after removing one or two vertices it has at most two odd components, after removing three it has at most three, and after any vertex deletion it has at most four.
-/

theorem even_graph_four_odd_component_bounds_has_perfect_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (heven : Even (Nat.card V))
    (hzero : ∀ S : Set V, S.ncard=0 →
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard = 0)
    (hone : ∀ S : Set V, S.ncard=1 →
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤ 2)
    (htwo : ∀ S : Set V, S.ncard=2 →
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤ 2)
    (hthree : ∀ S : Set V, S.ncard=3 →
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤ 3)
    (hall : ∀ S : Set V,
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤ 4) :
    ∃ P : G.Subgraph, P.IsPerfectMatching := by
  classical
  by_contra hn
  obtain ⟨S, hS⟩ := SimpleGraph.exists_isTutteViolator (G := G)
    (fun M hM => hn ⟨M, hM⟩) heven
  let W : Set V := ((⊤ : G.Subgraph).deleteVerts S).verts
  let H := ((⊤ : G.Subgraph).deleteVerts S).coe
  have hS' : S.ncard < H.oddComponents.ncard := hS
  have hpar := SimpleGraph.odd_ncard_oddComponents H
  have hcardW : Nat.card W = Fintype.card V - S.ncard := by
    rw [Nat.card_coe_set_eq]
    change (Set.univ \ S).ncard = _
    rw [Set.ncard_diff (Set.subset_univ S), Set.ncard_univ, Nat.card_eq_fintype_card]
  have hSle : S.ncard ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ S)
  have hev : Fintype.card V % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.even_iff.mp heven
  rw [hcardW, Nat.odd_iff, Nat.odd_iff] at hpar
  by_cases hs0 : S.ncard=0
  · have hh : H.oddComponents.ncard=0 := hzero S hs0
    omega
  · by_cases hs1 : S.ncard=1
    · have hh : H.oddComponents.ncard ≤ 2 := hone S hs1
      omega
    · by_cases hs2 : S.ncard=2
      · have hh : H.oddComponents.ncard ≤ 2 := htwo S hs2
        omega
      · by_cases hs3 : S.ncard=3
        · have hh : H.oddComponents.ncard ≤ 3 := hthree S hs3
          omega
        · have hh : H.oddComponents.ncard ≤ 4 := hall S
          omega
