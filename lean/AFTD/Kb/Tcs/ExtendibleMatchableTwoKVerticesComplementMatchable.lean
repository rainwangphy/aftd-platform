import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# extendible_matchable_two_k_vertices_complement_matchable

Topic: graphs   Node: 6ddfb3252e3d

Provenance: helper lemma. Matching-restriction ingredient for OP-1957 connected triple-twin cut.

In a finite k-extendible graph, the complement of any matchable set of exactly 2k vertices is matchable.
-/

lemma in1076_matching_twice_card
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

theorem extendible_matchable_two_k_vertices_complement_matchable
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (hG : is_k_extendable G k) (S : Set V)
    (hsize : S.ncard = 2 * k)
    (hS : ∃ M : (G.induce S).Subgraph, M.IsPerfectMatching) :
    ∃ P : (G.induce Sᶜ).Subgraph, P.IsPerfectMatching := by
  classical
  obtain ⟨P, hP⟩ := hS
  let f : (G.induce S) →g G :=
    { toFun := Subtype.val, map_rel' := by intro a b h; simpa using h }
  let M : G.Subgraph := P.map f
  have hf : Function.Injective f := fun a b h => Subtype.val_injective h
  have hMmatch : M.IsMatching := hP.1.map f hf
  have hMverts : M.verts = S := by
    rw [SimpleGraph.Subgraph.map_verts]
    ext v
    constructor
    · rintro ⟨x, -, rfl⟩; exact x.property
    · intro hv; exact ⟨⟨v, hv⟩, hP.2 ⟨v, hv⟩, rfl⟩
  have hMcard : M.edgeSet.ncard = k := by
    have h := in1076_matching_twice_card hMmatch
    rw [hMverts, hsize] at h
    omega
  obtain ⟨Q, hQ, hle⟩ := hG.2.2 M hMmatch hMcard
  have hmate {a b : V} (ha : a ∈ Sᶜ) (hab : Q.Adj a b) : b ∈ Sᶜ := by
    intro hb
    obtain ⟨c, hbc, -⟩ := hMmatch (v := b) (by rw [hMverts]; exact hb)
    have hQbc : Q.Adj b c := hle.2 hbc
    have hca : c = a := (hQ.1 (hQ.2 b)).unique hQbc hab.symm
    have hcS : c ∈ S := hMverts ▸ M.edge_vert hbc.symm
    exact ha (hca ▸ hcS)
  let g : (G.induce Sᶜ) →g G :=
    { toFun := Subtype.val, map_rel' := by intro a b h; simpa using h }
  let R : (G.induce Sᶜ).Subgraph := Q.comap g
  refine ⟨R, ?_⟩
  constructor
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
