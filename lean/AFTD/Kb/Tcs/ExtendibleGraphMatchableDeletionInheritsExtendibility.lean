import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IsMatchingSupDisjointEncard
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# extendible_graph_matchable_deletion_inherits_extendibility

Topic: graphs   Node: b4a783c248c4

Provenance: helper lemma. Induced-core reduction for the exact 2k separator in the OP-1957 two-bridge route.

If a graph is (r+j)-extendible and a 2j-vertex set U induces a perfect matching, then its induced complement is r-extendible, provided the complement has at least 2r+2 vertices and an r-matching.
-/

lemma extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M M' : SimpleGraph.Subgraph G) (hM : M.IsMatching) (hM' : M'.IsMatching) (hd : Disjoint M.verts M'.verts) :
    (M ⊔ M').IsMatching ∧ (M ⊔ M').edgeSet.ncard = M.edgeSet.ncard + M'.edgeSet.ncard := by
  have h := isMatching_sup_disjoint_encard M M' hM hM' hd
  refine ⟨h.1, ?_⟩
  rw [Set.ncard_def, h.2]
  have hfinM : M.edgeSet.Finite := Set.toFinite _
  have hfinM' : M'.edgeSet.Finite := Set.toFinite _
  rw [Set.Finite.encard_eq_coe hfinM, Set.Finite.encard_eq_coe hfinM']
  rw [← Set.ncard_def, ← Set.ncard_def]
  rw [← Nat.cast_add, ENat.toNat_natCast]

theorem extendible_graph_matchable_deletion_inherits_extendibility
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r j : ℕ)
    (hG : is_k_extendable G (r + j)) (hU : U.card = 2 * j)
    (hUmatch : ∃ P : (G.induce {v | v ∈ U}).Subgraph, P.IsPerfectMatching)
    (hCcard : 2 * r + 2 ≤ Fintype.card {v : V // v ∉ U})
    (hCmatch : ∃ M : (G.induce {v | v ∉ U}).Subgraph,
      M.IsMatching ∧ M.edgeSet.ncard = r) :
    is_k_extendable (G.induce {v | v ∉ U}) r := by
  refine ⟨hCcard, hCmatch, ?_⟩
  intro M hM hMcard
  obtain ⟨PU, hPU⟩ := hUmatch
  let S : Set V := {v : V | v ∈ U}
  have hSC : {v : V | v ∉ U} = Sᶜ := rfl
  let fU : (G.induce S) →g G :=
    { toFun := Subtype.val, map_rel' := by intro a b h; simpa using h }
  let fC : (G.induce Sᶜ) →g G :=
    { toFun := Subtype.val, map_rel' := by intro a b h; simpa using h }
  have hfU : Function.Injective fU := Subtype.val_injective
  have hfC : Function.Injective fC := Subtype.val_injective
  let MU : G.Subgraph := PU.map fU
  let MC : G.Subgraph := M.map fC
  have hMU_match : MU.IsMatching := hPU.1.map fU hfU
  have hMC_match : MC.IsMatching := hM.map fC hfC
  have hMU_verts : MU.verts = S := by
    rw [SimpleGraph.Subgraph.map_verts]
    ext v
    constructor
    · rintro ⟨x, -, rfl⟩; exact x.property
    · intro hv; exact ⟨⟨v, hv⟩, hPU.2 ⟨v, hv⟩, rfl⟩
  have hMU_card : MU.edgeSet.ncard = j := by
    have h := in1076_matching_twice_card hMU_match
    have hS : S.ncard = 2 * j := by
      have : S = ↑U := by ext; simp [S]
      rw [this, Set.ncard_coe_finset, hU]
    rw [hMU_verts, hS] at h
    omega
  have hMC_card : MC.edgeSet.ncard = r := by
    have hMC_verts_card : MC.verts.ncard = M.verts.ncard := by
      rw [SimpleGraph.Subgraph.map_verts]
      exact Set.ncard_image_of_injective M.verts hfC
    have h1 := in1076_matching_twice_card hMC_match
    have h2 := in1076_matching_twice_card hM
    rw [hMC_verts_card, ← h2, hMcard] at h1
    omega
  have hdisj : Disjoint MC.verts MU.verts := by
    rw [Set.disjoint_left]
    intro x hxMC hxMU
    rw [hMU_verts] at hxMU
    rw [SimpleGraph.Subgraph.map_verts] at hxMC
    obtain ⟨y, -, rfl⟩ := hxMC
    exact y.property hxMU
  have hsup := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard MC MU hMC_match hMU_match hdisj
  have htot_card : (MC ⊔ MU).edgeSet.ncard = r + j := by
    rw [hsup.2, hMC_card, hMU_card]
  obtain ⟨Q, hQ, hle⟩ := hG.2.2 (MC ⊔ MU) hsup.1 htot_card
  have hMC_le_Q : MC ≤ Q := le_trans le_sup_left hle
  have hMU_le_Q : MU ≤ Q := le_trans le_sup_right hle
  have hmate {a b : V} (ha : a ∈ Sᶜ) (hab : Q.Adj a b) : b ∈ Sᶜ := by
    intro hb
    obtain ⟨c, hbc, -⟩ := hMU_match (v := b) (by rw [hMU_verts]; exact hb)
    have hQbc : Q.Adj b c := hMU_le_Q.2 hbc
    have hca : c = a := (hQ.1 (hQ.2 b)).unique hQbc hab.symm
    have hcS : c ∈ S := hMU_verts ▸ MU.edge_vert hbc.symm
    exact ha (hca ▸ hcS)
  let R : (G.induce Sᶜ).Subgraph := Q.comap fC
  refine ⟨R, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨b, hab, huniq⟩ := hQ.1 (hQ.2 a.val)
    let b' : {v : V // v ∈ Sᶜ} := ⟨b, hmate a.property hab⟩
    refine ⟨b', ?_, ?_⟩
    · exact ⟨Q.adj_sub hab, hab⟩
    · intro c hc
      apply Subtype.ext
      exact huniq c.val hc.2
  · intro a
    exact hQ.2 a.val
  · rw [← SimpleGraph.Subgraph.map_le_iff_le_comap]
    exact hMC_le_Q
