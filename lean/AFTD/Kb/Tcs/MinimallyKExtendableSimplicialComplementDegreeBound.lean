import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.MatchingFourSwitchSimplicialComplementZeroCodegree
import AFTD.Kb.Tcs.ForcedMatchingEdgeBlocksFourAndSixSwitches
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual

/-!
# minimally_k_extendable_simplicial_complement_degree_bound

Topic: graphs   Node: 0d068d3fd5f2

Provenance: helper lemma. OP-1957: simplicial complement neighborhood and zero-codegree edge selection.

For a minimally k-extendable graph on 2k+2j vertices, j at least two, a complement-simplicial vertex satisfying the displayed numerical two-neighborhood bound forces minimum degree at most 2k+1.
-/

theorem minimally_k_extendable_simplicial_complement_degree_bound
    (k j : ℕ) (hj : 2 ≤ j) (G : SimpleGraph (Fin (2*k+2*j))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (u : Fin (2*k+2*j))
    (hclique : ∀ a b, a ≠ b → (Gᶜ).Adj u a → (Gᶜ).Adj u b → (Gᶜ).Adj a b)
    (hcount : 3 + (Gᶜ).degree u + (Gᶜ).degree u * (2*j-3-(Gᶜ).degree u) ≤ 2*k+2*j) :
    G.minDegree ≤ 2*k+1 := by
  classical
  by_contra hlt
  have hdeg : 2*k+2 ≤ G.minDegree := by omega
  have hdegH : ∀ x : Fin (2*k+2*j), (Gᶜ).degree x ≤ 2*j-3 := by
    intro x
    have h1 := SimpleGraph.degree_compl G x
    rw [Fintype.card_fin] at h1
    have h2 := SimpleGraph.minDegree_le_degree G x
    omega
  let A : Finset (Fin (2*k+2*j)) := (Gᶜ).neighborFinset u
  have hAcard : A.card = (Gᶜ).degree u := SimpleGraph.card_neighborFinset_eq_degree (Gᶜ) u
  let O : Fin (2*k+2*j) → Finset (Fin (2*k+2*j)) := fun a => (Gᶜ).neighborFinset a \ insert u A
  let S : Finset (Fin (2*k+2*j)) := insert u (A ∪ A.biUnion O)
  have hu_notin_A : u ∉ A := by
    intro h
    exact SimpleGraph.irrefl (Gᶜ) ((SimpleGraph.mem_neighborFinset (Gᶜ) u u).mp h)
  have hOp : ∀ a ∈ A, (O a).card ≤ 2*j-3 - A.card := by
    intro a ha
    have hAa : (Gᶜ).Adj u a := (SimpleGraph.mem_neighborFinset (Gᶜ) u a).mp ha
    have hsubset_a : ({a} : Finset (Fin (2*k+2*j))) ⊆ insert u A := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]; exact Finset.mem_insert_of_mem ha
    have hsub1 : (insert u A) \ {a} ⊆ (Gᶜ).neighborFinset a := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
      obtain ⟨hxin, hxa⟩ := hx
      rw [SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_insert.mp hxin with rfl | hxA
      · exact hAa.symm
      · have hxadj : (Gᶜ).Adj u x := (SimpleGraph.mem_neighborFinset (Gᶜ) u x).mp hxA
        exact hclique a x (fun h => hxa h.symm) hAa hxadj
    have hsub2 : (insert u A) \ {a} ⊆ (Gᶜ).neighborFinset a ∩ insert u A := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨hsub1 hx, (Finset.mem_sdiff.mp hx).1⟩
    have hcard1 : ((insert u A) \ {a}).card = A.card := by
      rw [Finset.card_sdiff_of_subset hsubset_a, Finset.card_singleton,
          Finset.card_insert_of_notMem hu_notin_A]
      omega
    have hle : A.card ≤ ((Gᶜ).neighborFinset a ∩ insert u A).card := by
      calc A.card = ((insert u A) \ {a}).card := hcard1.symm
        _ ≤ _ := Finset.card_le_card hsub2
    have hIle : ((Gᶜ).neighborFinset a ∩ insert u A).card ≤ ((Gᶜ).neighborFinset a).card :=
      Finset.card_le_card Finset.inter_subset_left
    have hBcard : ((Gᶜ).neighborFinset a).card = (Gᶜ).degree a :=
      SimpleGraph.card_neighborFinset_eq_degree (Gᶜ) a
    have hdega : (Gᶜ).degree a ≤ 2*j-3 := hdegH a
    have hOdef : O a = (Gᶜ).neighborFinset a \ insert u A := rfl
    have hIcomm : insert u A ∩ (Gᶜ).neighborFinset a = (Gᶜ).neighborFinset a ∩ insert u A :=
      Finset.inter_comm _ _
    have hOeq : (O a).card = ((Gᶜ).neighborFinset a).card - ((Gᶜ).neighborFinset a ∩ insert u A).card := by
      rw [hOdef, Finset.card_sdiff, hIcomm]
    omega
  have hScard : S.card ≤ 1 + A.card + A.card * (2*j-3-A.card) := by
    have h1 : S.card ≤ (A ∪ A.biUnion O).card + 1 := by
      have h := Finset.card_insert_le u (A ∪ A.biUnion O)
      simpa [S] using h
    have h2 : (A ∪ A.biUnion O).card ≤ A.card + (A.biUnion O).card := Finset.card_union_le _ _
    have h3 : (A.biUnion O).card ≤ ∑ a ∈ A, (O a).card := Finset.card_biUnion_le
    have h4 : (∑ a ∈ A, (O a).card) ≤ ∑ a ∈ A, (2*j-3-A.card) :=
      Finset.sum_le_sum (fun a ha => hOp a ha)
    have h5 : (∑ a ∈ A, (2*j-3-A.card)) = A.card * (2*j-3-A.card) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    omega
  have hSlt : S.card < 2*k+2*j := by
    have h := hcount
    rw [← hAcard] at h
    omega
  have huniv : ¬ ((Finset.univ : Finset (Fin (2*k+2*j))) ⊆ S) := by
    intro hsub
    have hEq : S = (Finset.univ : Finset (Fin (2*k+2*j))) :=
      Finset.Subset.antisymm (Finset.subset_univ S) hsub
    rw [hEq, Finset.card_univ, Fintype.card_fin] at hSlt
    exact Nat.lt_irrefl _ hSlt
  obtain ⟨v, -, hvS⟩ := Finset.not_subset.mp huniv
  have hv_not_A : v ∉ A := by
    intro h
    exact hvS (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
  have huv : G.Adj u v := by
    by_contra h
    have hne : u ≠ v := by
      intro he
      exact hvS (he ▸ Finset.mem_insert_self u (A ∪ A.biUnion O))
    exact hv_not_A ((SimpleGraph.mem_neighborFinset (Gᶜ) u v).mpr ((SimpleGraph.compl_adj G u v).mpr ⟨hne, h⟩))
  have hsep : ∀ a, (Gᶜ).Adj u a → ¬ (Gᶜ).Adj v a := by
    intro a hua hva
    have haA : a ∈ A := (SimpleGraph.mem_neighborFinset (Gᶜ) u a).mpr hua
    have hBa : v ∈ (Gᶜ).neighborFinset a := (SimpleGraph.mem_neighborFinset (Gᶜ) a v).mpr hva.symm
    have hsub : (Gᶜ).neighborFinset a ⊆ insert u A ∪ O a := by
      intro x hx
      by_cases hx' : x ∈ insert u A
      · exact Finset.mem_union_left _ hx'
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hx'⟩)
    have hsubS : insert u A ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with heq | hA
      · rw [heq]; exact Finset.mem_insert_self u _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hA)
    have hOS : O a ⊆ S := by
      intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, haA, hx⟩))
    have hvS' : v ∈ S := by
      have h := hsub hBa
      rcases Finset.mem_union.mp h with h' | h'
      · exact hsubS h'
      · exact hOS h'
    exact hvS hvS'
  obtain ⟨R, hRc, hu, hv, ⟨P, hP⟩, hnoPM⟩ :=
    k_extendable_essential_edge_has_forced_matching_residual (2*k+2*j) k G u v huv hmin.1 (hmin.2 _ huv)
  let GR : SimpleGraph {a // a ∈ R} := G.induce {a | a ∈ R}
  let u' : {a // a ∈ R} := ⟨u, hu⟩
  let v' : {a // a ∈ R} := ⟨v, hv⟩
  have hdegGR : ∃ x y : {a // a ∈ R}, x ≠ y ∧ GR.Adj v' x ∧ GR.Adj v' y := by
    have hcomplcard : (Finset.univ \ R).card = 2*k := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ, Fintype.card_fin]
      omega
    have hsub : G.neighborFinset v ⊆ R.filter (fun y => G.Adj v y) ∪ (Finset.univ \ R) := by
      intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      by_cases hyR : y ∈ R
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyR, hy⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyR⟩)
    have hcardle : (G.neighborFinset v).card ≤ (R.filter (fun y => G.Adj v y)).card + 2*k := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (R.filter (fun y => G.Adj v y)) (Finset.univ \ R)
      rw [hcomplcard] at h2
      omega
    have hdegv : 2*k+2 ≤ G.degree v := le_trans hdeg (SimpleGraph.minDegree_le_degree G v)
    have hnecard : (G.neighborFinset v).card = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
    have hgt : 1 < (R.filter (fun y => G.Adj v y)).card := by omega
    obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Finset.one_lt_card.mp hgt
    refine ⟨⟨y1, (Finset.mem_filter.mp hy1).1⟩, ⟨y2, (Finset.mem_filter.mp hy2).1⟩, ?_, ?_, ?_⟩
    · intro he
      exact hy12 (Subtype.ext_iff.mp he)
    · change G.Adj v y1
      exact (Finset.mem_filter.mp hy1).2
    · change G.Adj v y2
      exact (Finset.mem_filter.mp hy2).2
  have hGRadj : ∀ x y : {a // a ∈ R}, GR.Adj x y ↔ G.Adj x.1 y.1 := by
    intro x y
    exact SimpleGraph.induce_adj
  have hGRc : ∀ x y : {a // a ∈ R}, (GRᶜ).Adj x y ↔ (Gᶜ).Adj x.1 y.1 := by
    intro x y
    constructor
    · intro h
      rw [SimpleGraph.compl_adj] at h ⊢
      exact ⟨fun he => h.1 (Subtype.ext he), fun hg => h.2 ((hGRadj x y).mpr hg)⟩
    · intro h
      rw [SimpleGraph.compl_adj] at h ⊢
      exact ⟨fun he => h.1 (congrArg Subtype.val he), fun hg => h.2 ((hGRadj x y).mp hg)⟩
  have hforced : ∀ Q : GR.Subgraph, Q.IsPerfectMatching → Q.Adj u' v' := by
    intro Q hQ
    by_contra hn
    apply hnoPM
    refine ⟨⟨Q.verts, Q.Adj, ?_, Q.edge_vert, Q.symm⟩, ?_⟩
    · intro x y hxy
      refine SimpleGraph.deleteEdges_adj.mpr ⟨Q.adj_sub hxy, ?_⟩
      intro he
      have hsym : s(x, y) = s(u', v') := by simpa using he
      rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hn hxy
      · exact hn hxy.symm
    · exact hQ
  have huvP : P.Adj u' v' := hforced P hP
  have hcliqueGR : ∀ a b : {a // a ∈ R}, a ≠ b → (GRᶜ).Adj u' a → (GRᶜ).Adj u' b → (GRᶜ).Adj a b := by
    intro a b hab hua hub
    rw [hGRc] at hua hub ⊢
    exact hclique a.1 b.1 (fun h => hab (Subtype.ext h)) hua hub
  have hsepGR : ∀ a : {a // a ∈ R}, (GRᶜ).Adj u' a → ¬ (GRᶜ).Adj v' a := by
    intro a hua
    rw [hGRc] at hua
    rw [hGRc]
    exact hsep a.1 hua
  have hblock := forced_matching_edge_blocks_four_and_six_switches GR P hP u' v' huvP hforced
  obtain ⟨a, b, hinj, hPab, hva, hub⟩ :=
    matching_four_switch_simplicial_complement_zero_codegree GR P hP u' v' huvP hdegGR hcliqueGR hsepGR
  exact hblock.1 ⟨a, b, hinj, hPab, hva, hub⟩
