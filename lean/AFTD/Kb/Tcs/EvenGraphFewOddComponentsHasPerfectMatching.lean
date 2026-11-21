import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeCommonNonneighborsBelowMinDegreeIsBridge
import AFTD.Kb.Tcs.Op2037SubgraphFintype

/-!
# even_graph_few_odd_components_has_perfect_matching

Topic: graphs   Node: 9f0b878685dd

Provenance: helper lemma. OP-1957: odd-component parity helper for four-block matching obstructions.

An even-order finite graph has a perfect matching if its odd-component count after deleting any vertex set is at most three, is at most two after deleting one vertex, and is zero after deleting no vertices.
-/

theorem even_graph_few_odd_components_has_perfect_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (heven : Even (Nat.card V))
    (hzero : ∀ S : Set V, S.ncard = 0 →
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard = 0)
    (hone : ∀ S : Set V, S.ncard = 1 →
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤ 2)
    (hall : ∀ S : Set V,
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤ 3) :
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
  have hb : H.oddComponents.ncard ≤ 3 := hall S
  by_cases hs0 : S.ncard = 0
  · have hh : H.oddComponents.ncard = 0 := hzero S hs0
    omega
  · by_cases hs1 : S.ncard = 1
    · have hh : H.oddComponents.ncard ≤ 2 := hone S hs1
      omega
    · omega
