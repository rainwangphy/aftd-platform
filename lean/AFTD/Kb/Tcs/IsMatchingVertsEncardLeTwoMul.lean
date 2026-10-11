import AFTD.Prelude

/-!
# isMatching_verts_encard_le_two_mul

Topic: graphs   Node: 6318d5686792

Provenance: helper lemma. step towards vertex_cover_num_le_two_mul_matching_num

For any matching M in a graph G, the number of vertices in M is at most twice the number of edges in M.
-/

noncomputable def isMatching_verts_encard_le_two_mul_endpoint {V : Type*} {G : SimpleGraph V} (M : G.Subgraph)
    (x : M.edgeSet × Fin 2) : M.verts :=
  let p := Quot.out x.1.val
  have hAdj : M.Adj p.1 p.2 := by
    have h := x.1.2
    have hq := Quot.out_eq x.1.val
    rw [← hq] at h
    exact M.mem_edgeSet.mp h
  Fin.cases ⟨p.1, M.edge_vert hAdj⟩ (fun _ => ⟨p.2, M.edge_vert hAdj.symm⟩) x.2

lemma isMatching_verts_encard_le_two_mul_endpoint_surjective {V : Type*} {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) : Function.Surjective (isMatching_verts_encard_le_two_mul_endpoint M) := by
  intro ⟨v, hv⟩
  obtain ⟨w, hw, -⟩ := hM hv
  have he : s(v, w) ∈ M.edgeSet := M.mem_edgeSet.mpr hw
  let e : M.edgeSet := ⟨s(v, w), he⟩
  have hq : Quot.mk (Sym2.Rel V) (Quot.out e.val) = s(v, w) := Quot.out_eq e.val
  have h_eq : s((Quot.out e.val).1, (Quot.out e.val).2) = s(v, w) := hq
  rw [Sym2.eq_iff] at h_eq
  rcases h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · use (e, 0)
    exact Subtype.ext h1
  · use (e, 1)
    exact Subtype.ext h2

/-- In any simple graph, the number of vertices in a matching M is at most twice the number of edges in M. -/
theorem isMatching_verts_encard_le_two_mul {V : Type*} {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) : M.verts.encard ≤ 2 * M.edgeSet.encard := by
  have hsurj := isMatching_verts_encard_le_two_mul_endpoint_surjective M hM
  have hle : ENat.card M.verts ≤ ENat.card (M.edgeSet × Fin 2) :=
    ENat.card_le_card_of_injective (Function.injective_surjInv hsurj)
  rw [ENat.card_prod] at hle
  have hFin2 : ENat.card (Fin 2) = 2 := by simp
  rw [hFin2, mul_comm, ENat.card_coe_set_eq, ENat.card_coe_set_eq] at hle
  exact hle
