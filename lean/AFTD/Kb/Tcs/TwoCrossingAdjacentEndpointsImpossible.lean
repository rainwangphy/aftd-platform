import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.HighMinDegreeMatchingExtendsToSize
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility
import AFTD.Kb.Tcs.PerfectMatchingBalancedCutInternalEdgeCountsEqual
import AFTD.Kb.Tcs.PerfectMatchingInducedEdgesFormMatching
import AFTD.Kb.Tcs.MatchingEdgesInsideInduced

/-!
# two_crossing_adjacent_endpoints_impossible

Topic: graphs   Node: d52d225d6a48

Provenance: helper lemma. Balanced-cut matching reduction for OP-1957; https://arxiv.org/abs/1011.3384.

With the displayed extendibility, degree and balanced-half maximum matching assumptions, two distinct vertices unmatched by a maximum matching cannot cross to adjacent vertices on the opposite side.
-/

theorem two_crossing_adjacent_endpoints_impossible
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hdegree : ∀ v, 2*k ≤ (G.neighborFinset v).card)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching)
    (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hNC : N.verts ⊆ ((C : Set (Fin (4*k)))ᶜ))
    (hmaxM : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin (4*k))) → T.edgeSet.ncard ≤ M.edgeSet.ncard)
    (hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ ((C : Set (Fin (4*k)))ᶜ) → T.edgeSet.ncard ≤ N.edgeSet.ncard)
    (heq : M.edgeSet.ncard = N.edgeSet.ncard) (hroom : M.edgeSet.ncard + 2 ≤ k)
    (u v x y : Fin (4*k)) (hu : u ∈ C) (hv : v ∈ C) (huv : u ≠ v)
    (huM : u ∉ M.verts) (hvM : v ∉ M.verts)
    (hx : x ∉ C) (hy : y ∉ C)
    (hux : G.Adj u x) (hvy : G.Adj v y) (hxy : G.Adj x y) : False := by
  set_option maxHeartbeats 4000000 in
    classical
    have oneEdge : ∀ (p q : Fin (4*k)), G.Adj p q →
        ∃ E : G.Subgraph, E.IsMatching ∧ E.edgeSet.ncard = 1 ∧
          E.verts = ({p,q} : Set (Fin (4*k))) ∧ E.Adj p q := by
      intro p q hpq
      let f : Fin 1 → Fin (4*k) := fun _ => p
      let g : Fin 1 → Fin (4*k) := fun _ => q
      obtain ⟨E,hE,hcard,hverts⟩ := indexed_disjoint_cross_edges_form_matching G 1 f g
        (by intro i j h; exact Subsingleton.elim i j)
        (by intro i j h; exact Subsingleton.elim i j)
        (by intro i j; exact G.ne_of_adj hpq)
        (by intro i; exact hpq)
      have hv : E.verts = ({p,q} : Set (Fin (4*k))) := by
        rw [hverts]
        ext z
        simp [f,g,or_comm]
      have hp : p ∈ E.verts := by rw [hv]; simp
      obtain ⟨w,hpw,hw⟩ := hE hp
      have hwv := E.edge_vert hpw.symm
      rw [hv] at hwv
      have hwq : w=q := by
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hwv
        rcases hwv with h | h
        · exact False.elim ((G.ne_of_adj (E.adj_sub hpw)) h.symm)
        · exact h
      refine ⟨E,hE,hcard,hv,?_⟩
      simpa [hwq] using hpw
    obtain ⟨E1,hE1,hE1card,hE1verts,hE1adj⟩ := oneEdge u x hux
    obtain ⟨E2,hE2,hE2card,hE2verts,hE2adj⟩ := oneEdge v y hvy
    have hEdis : Disjoint E1.verts E2.verts := by
      rw [hE1verts,hE2verts]
      apply Set.disjoint_left.mpr
      intro z hz1 hz2
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz1 hz2
      rcases hz1 with h1 | h1 <;> rcases hz2 with h2 | h2 <;> subst z <;> simp_all [G.ne_of_adj hxy]
    have hE := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard E1 E2 hE1 hE2 hEdis
    have hME : Disjoint M.verts (E1 ⊔ E2).verts := by
      apply Set.disjoint_left.mpr
      intro z hzM hzE
      change z ∈ E1.verts ∪ E2.verts at hzE
      rw [hE1verts,hE2verts] at hzE
      have hzC := hMC hzM
      simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff] at hzE
      rcases hzE with (h | h) | (h | h) <;> subst z <;> simp_all
    have hME' := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard M (E1 ⊔ E2) hM hE.1 hME
    have hMEk : (M ⊔ (E1 ⊔ E2)).edgeSet.ncard ≤ k := by rw [hME'.2,hE.2,hE1card,hE2card]; omega
    obtain ⟨T,hT,hMET,hTk⟩ := high_min_degree_matching_extends_to_size G k hext.1 hdegree (M ⊔ (E1 ⊔ E2)) hME'.1 hMEk
    obtain ⟨P,hP,hTP⟩ := hext.2.2 T hT hTk
    have hMP : M ≤ P := le_trans (le_trans le_sup_left hMET) hTP
    have hE1P : E1 ≤ P := le_trans (le_trans (le_trans le_sup_left le_sup_right) hMET) hTP
    have hE2P : E2 ≤ P := le_trans (le_trans (le_trans le_sup_right le_sup_right) hMET) hTP
    have hCcomp : ((Cᶜ : Finset (Fin (4*k))) : Set (Fin (4*k))) = (C : Set (Fin (4*k)))ᶜ := by ext z; simp
    obtain ⟨Q,hQ,hQC,hQP,hQE⟩ := perfect_matching_induced_edges_form_matching G P hP C
    obtain ⟨R,hR,hRC,hRP,hRE⟩ := perfect_matching_induced_edges_form_matching G P hP (Cᶜ : Finset (Fin (4*k)))
    have hMsub := matching_edges_inside_induced G M P hMP C hMC
    have hMbound := Set.ncard_le_ncard hMsub (Set.toFinite _)
    have hQbound := hmaxM Q hQ hQC
    rw [← hQE] at hMbound
    have hQcard : Q.edgeSet.ncard = M.edgeSet.ncard := by omega
    have hbal := perfect_matching_balanced_cut_internal_edge_counts_equal G P hP C (by simp only [Fintype.card_fin,hcard]; omega)
    rw [← hCcomp,← hQE,← hRE,hQcard,heq] at hbal
    have hxR : x ∉ R.verts := by
      intro hxR
      obtain ⟨z,hxz,huniq⟩ := hR hxR
      have hxu := (hP.1 (hP.2 x)).unique (hRP.2 hxz) ((hE1P.2 hE1adj).symm)
      have hzC : z ∉ C := by simpa using hRC (R.edge_vert hxz.symm)
      exact hzC (hxu.symm ▸ hu)
    have hyR : y ∉ R.verts := by
      intro hyR
      obtain ⟨z,hyz,huniq⟩ := hR hyR
      have hyv := (hP.1 (hP.2 y)).unique (hRP.2 hyz) ((hE2P.2 hE2adj).symm)
      have hzC : z ∉ C := by simpa using hRC (R.edge_vert hyz.symm)
      exact hzC (hyv.symm ▸ hv)
    let f : Fin 1 → Fin (4*k) := fun _ => x
    let g : Fin 1 → Fin (4*k) := fun _ => y
    obtain ⟨F,hF,hFcard,hFverts⟩ := indexed_disjoint_cross_edges_form_matching G 1 f g
      (by intro i j h; exact Subsingleton.elim i j)
      (by intro i j h; exact Subsingleton.elim i j)
      (by intro i j; exact G.ne_of_adj hxy)
      (by intro i; exact hxy)
    have hRF : Disjoint R.verts F.verts := by
      apply Set.disjoint_left.mpr
      intro z hzR hzF
      rw [hFverts] at hzF
      rcases hzF with ⟨i,hi⟩ | ⟨i,hi⟩
      · apply hxR; simpa [f,hi] using hzR
      · apply hyR; simpa [g,hi] using hzR
    have hRF' := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard R F hR hF hRF
    have hsub : (R ⊔ F).verts ⊆ ((C : Set (Fin (4*k)))ᶜ) := by
      intro z hz
      change z ∈ R.verts ∪ F.verts at hz
      rcases hz with hzR | hzF
      · simpa using hRC hzR
      · rw [hFverts] at hzF
        rcases hzF with ⟨i,hi⟩ | ⟨i,hi⟩
        · simpa [f,hi] using hx
        · simpa [g,hi] using hy
    have hmax := hmaxN (R ⊔ F) hRF'.1 hsub
    rw [hRF'.2,hFcard,hbal] at hmax
    omega
