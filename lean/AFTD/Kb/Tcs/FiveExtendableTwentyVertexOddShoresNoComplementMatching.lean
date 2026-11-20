import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# five_extendable_twenty_vertex_odd_shores_no_complement_matching

Topic: graphs   Node: 7228e8068ad9

Provenance: helper lemma. Triple-twin cut obstruction used in the two-critical-edge branch of OP-1957.

Let G be a 5-extendible graph on 20 vertices, and let disjoint sets T and N have 3 and 7 vertices with no edges between them. The induced graph on the ten vertices outside T and N has no perfect matching.
-/

private lemma five_extendable_twenty_vertex_odd_shores_no_complement_matching_two_mul_edge_ncard
    {V : Type*} [Fintype V] {G : SimpleGraph V} {M : G.Subgraph}
    (h : M.IsMatching) : 2 * M.edgeSet.ncard = M.verts.ncard := by
  classical
  have key : ∀ e : M.edgeSet, Fintype.card {v : M.verts // h.toEdge v = e} = 2 := by
    rintro ⟨x, hx⟩
    revert hx
    induction x using Sym2.ind with
    | _ a b =>
      intro hx
      have hab : M.Adj a b := SimpleGraph.Subgraph.mem_edgeSet.mp hx
      have h1 : (⟨s(a, b), hx⟩ : M.edgeSet) =
          ⟨s(a, b), SimpleGraph.Subgraph.mem_edgeSet.mpr hab⟩ := Subtype.ext rfl
      have hEq : h.toEdge ⁻¹' {⟨s(a, b), hx⟩} = {⟨a, hab.fst_mem⟩, ⟨b, hab.snd_mem⟩} := by
        rw [h1]
        exact h.toEdge_preimage_singleton hab
      have hset2 : {v : M.verts | h.toEdge v = (⟨s(a, b), hx⟩ : M.edgeSet)}
          = ({⟨a, hab.fst_mem⟩, ⟨b, hab.snd_mem⟩} : Set M.verts) := by
        ext v
        have hmem := Set.ext_iff.mp hEq v
        simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
          Set.mem_insert_iff] using hmem
      calc Fintype.card {v : M.verts // h.toEdge v = (⟨s(a, b), hx⟩ : M.edgeSet)}
          = Fintype.card ↥({⟨a, hab.fst_mem⟩, ⟨b, hab.snd_mem⟩} : Set M.verts) :=
            Fintype.card_congr (Equiv.setCongr hset2)
        _ = 2 := by
            rw [← Set.toFinset_card]
            have hne : (⟨a, hab.fst_mem⟩ : M.verts) ≠ ⟨b, hab.snd_mem⟩ := by
              simp [G.ne_of_adj (M.adj_sub hab)]
            simp [hne]
  have hsum : Fintype.card M.verts =
      ∑ e : M.edgeSet, Fintype.card {v : M.verts // h.toEdge v = e} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv h.toEdge).symm
  have h1 : Fintype.card M.verts = 2 * Fintype.card M.edgeSet := by
    rw [hsum]
    simp [key, Nat.mul_comm]
  have hv : M.verts.ncard = Fintype.card M.verts := by
    rw [Set.ncard_eq_toFinset_card M.verts, Set.toFinite_toFinset]
    exact Set.toFinset_card M.verts
  have he : M.edgeSet.ncard = Fintype.card M.edgeSet := by
    rw [Set.ncard_eq_toFinset_card M.edgeSet, Set.toFinite_toFinset]
    exact Set.toFinset_card M.edgeSet
  rw [hv, he, h1]

theorem five_extendable_twenty_vertex_odd_shores_no_complement_matching
    (G : SimpleGraph (Fin 20)) (hG : is_k_extendable G 5)
    (T N : Finset (Fin 20)) (ht : T.card = 3) (hn : N.card = 7)
    (hdisj : Disjoint T N)
    (hcross : ∀ a ∈ T, ∀ b ∈ N, ¬ G.Adj a b) :
    ¬ ∃ P : (G.induce {v | v ∉ T ∧ v ∉ N}).Subgraph, P.IsPerfectMatching := by
  classical
  obtain ⟨-, -, hext⟩ := hG
  rintro ⟨P, hP⟩
  let S : Set (Fin 20) := {v | v ∉ T ∧ v ∉ N}
  let f : (G.induce S) →g G :=
    { toFun := Subtype.val, map_rel' := by intro a b h; simpa using h }
  let M : G.Subgraph := P.map f
  have hMinj : Function.Injective f := fun a b h => Subtype.val_injective h
  have hMmatch : M.IsMatching := hP.1.map f hMinj
  have hMverts : M.verts = S := by
    rw [SimpleGraph.Subgraph.map_verts]
    ext v
    constructor
    · rintro ⟨x, -, rfl⟩; exact x.property
    · intro hv; exact ⟨⟨v, hv⟩, hP.2 ⟨v, hv⟩, rfl⟩
  have hSncard : S.ncard = 10 := by
    have hSeq : S = ↑(Finset.univ \ (T ∪ N)) := by
      ext v; simp [S]
    rw [hSeq, Set.ncard_coe_finset, Finset.card_sdiff]
    have hcard : (T ∪ N).card = 10 := by
      rw [Finset.card_union_of_disjoint hdisj, ht, hn]
    simp [hcard]
  have hMcard : M.edgeSet.ncard = 5 := by
    have h := five_extendable_twenty_vertex_odd_shores_no_complement_matching_two_mul_edge_ncard
      hMmatch
    rw [hMverts, hSncard] at h
    omega
  obtain ⟨P', hP', hle⟩ := hext M hMmatch hMcard
  let R : G.Subgraph := P'.induce (↑T : Set (Fin 20))
  have hRverts : R.verts = ↑T := rfl
  have hRmatch : R.IsMatching := by
    intro v hv
    rw [hRverts] at hv
    obtain ⟨w, hw, hwuniq⟩ := hP'.1 (hP'.2 v)
    have hwN : w ∉ N := by
      intro hwN
      exact hcross v hv w hwN (P'.adj_sub hw)
    have hwS : w ∉ S := by
      intro hwS
      obtain ⟨u, hMu, -⟩ := hMmatch (v := w) (by rw [hMverts]; exact hwS)
      have hPu : P'.Adj w u := hle.2 hMu
      have huv : u = v := (hP'.1 (hP'.2 w)).unique hPu hw.symm
      have huS : u ∈ S := hMverts ▸ M.edge_vert hMu.symm
      rw [huv] at huS
      exact huS.1 hv
    have hwT : w ∈ T := by
      by_contra hwT
      exact hwS ⟨hwT, hwN⟩
    refine ⟨w, ⟨hv, hwT, hw⟩, ?_⟩
    rintro y ⟨-, -, hPy⟩
    exact hwuniq y hPy
  have hEven : Even R.verts.toFinset.card := hRmatch.even_card
  have hTeq : R.verts.toFinset = T := by
    rw [hRverts]
    ext v
    simp
  rw [hTeq, ht] at hEven
  obtain ⟨k, hk⟩ := hEven
  omega
