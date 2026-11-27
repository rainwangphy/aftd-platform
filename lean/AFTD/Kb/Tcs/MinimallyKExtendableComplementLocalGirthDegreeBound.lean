import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.MatchingShortSwitchComplementLocalGirthFive
import AFTD.Kb.Tcs.ForcedMatchingEdgeBlocksFourAndSixSwitches
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.C

/-!
# minimally_k_extendable_complement_local_girth_degree_bound

Topic: graphs   Node: adabc36ba22b

Provenance: helper lemma. OP-1957: the complementary local-girth obstruction, pending formal proof.

For a minimally k-extendable graph on 2k+2j vertices with j at least two, if some vertex belongs to no triangle or four-cycle of the complement, then the graph has minimum degree at most 2k+1.
-/

theorem in1163_pm_comap {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G →g G') (hf : Function.Bijective f) (Q : G'.Subgraph) (hQ : Q.IsPerfectMatching)
    (hadj : ∀ a b, Q.Adj (f a) (f b) → G.Adj a b) : (Q.comap f).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hQ ⊢
  intro a
  obtain ⟨w, hw, hu⟩ := hQ (f a)
  obtain ⟨b, rfl⟩ := hf.2 w
  refine ⟨b, ⟨hadj a b hw, hw⟩, ?_⟩
  intro c hc
  exact hf.1 (hu _ hc.2)

theorem minimally_k_extendable_complement_local_girth_degree_bound
    (k j : ℕ) (hj : 2 ≤ j) (G : SimpleGraph (Fin (2*k+2*j))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (u : Fin (2*k+2*j))
    (htri : ∀ a b, (Gᶜ).Adj u a → (Gᶜ).Adj u b → a ≠ b → ¬ (Gᶜ).Adj a b)
    (hsquare : ∀ a b x, (Gᶜ).Adj u a → (Gᶜ).Adj u b → a ≠ b → x ≠ u → ¬ ((Gᶜ).Adj a x ∧ (Gᶜ).Adj b x)) :
    G.minDegree ≤ 2*k+1 := open SimpleGraph in by
  classical
  by_contra hlt
  have hdeg : 2*k+2 ≤ G.minDegree := by omega
  obtain ⟨v, huv⟩ : ∃ v, G.Adj u v := by
    have h := G.minDegree_le_degree u
    have : 0 < (G.neighborFinset u).card := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp this
    exact ⟨v, (mem_neighborFinset _ _ _).1 hv⟩
  obtain ⟨R, hRc, hu, hv, ⟨P, hP⟩, hnoPM⟩ :=
    k_extendable_essential_edge_has_forced_matching_residual _ k G u v huv hmin.1 (hmin.2 _ huv)
  have hcardW : Fintype.card ({a | a ∈ R} : Set (Fin (2*k+2*j))) = 2*j := by
    rw [Fintype.card_subtype]
    simp only [Set.mem_ofPred_eq, Finset.filter_mem_eq_inter, Finset.univ_inter]
    omega
  let e : ({a | a ∈ R} : Set (Fin (2*k+2*j))) ≃ Fin (2*j) := Fintype.equivFinOfCardEq hcardW
  let GR := G.induce {a | a ∈ R}
  let H : SimpleGraph (Fin (2*j)) := GR.comap e.symm
  have hHadj : ∀ x y, H.Adj x y ↔ G.Adj (e.symm x).1 (e.symm y).1 := fun x y => Iff.rfl
  have hHc : ∀ x y, (Hᶜ).Adj x y ↔ (Gᶜ).Adj (e.symm x).1 (e.symm y).1 := by
    intro x y
    rw [compl_adj, compl_adj, hHadj]
    constructor
    · rintro ⟨hne, hn⟩
      refine ⟨fun h => hne (e.symm.injective (Subtype.ext h)), hn⟩
    · rintro ⟨hne, hn⟩
      exact ⟨fun h => hne (h ▸ rfl), hn⟩
  let f1 : H →g GR := ⟨e.symm, fun h => h⟩
  have hPH : (P.comap f1).IsPerfectMatching :=
    in1163_pm_comap f1 e.symm.bijective P hP (fun a b h => P.adj_sub h)
  let u' : ({a | a ∈ R} : Set (Fin (2*k+2*j))) := ⟨u, hu⟩
  let v' : ({a | a ∈ R} : Set (Fin (2*k+2*j))) := ⟨v, hv⟩
  have hforced : ∀ Q : H.Subgraph, Q.IsPerfectMatching → Q.Adj (e u') (e v') := by
    intro Q hQ
    by_contra hn
    apply hnoPM
    let f2 : (GR.deleteEdges {s(u', v')}) →g H :=
      ⟨e, fun {x y} h => by
        have h' := (SimpleGraph.deleteEdges_adj.mp h).1
        show GR.Adj (e.symm (e x)) (e.symm (e y))
        simpa using h'⟩
    refine ⟨Q.comap f2, in1163_pm_comap f2 e.bijective Q hQ ?_⟩
    intro a b hab
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨?_, ?_⟩
    · have h := Q.adj_sub hab
      change GR.Adj (e.symm (e a)) (e.symm (e b)) at h
      simpa using h
    · intro hs
      simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hn hab
      · exact hn hab.symm
  have huvH : (P.comap f1).Adj (e u') (e v') := hforced _ hPH
  have hblock := forced_matching_edge_blocks_four_and_six_switches H (P.comap f1) hPH
    (e u') (e v') huvH hforced
  have hdegH : ∀ x, 2 ≤ H.degree x := by
    intro x
    set a := e.symm x with ha
    have hsub : G.neighborFinset a.1 ⊆ R.filter (fun y => G.Adj a.1 y) ∪ (Finset.univ \ R) := by
      intro y hy
      rw [mem_neighborFinset] at hy
      by_cases hyR : y ∈ R
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hyR, hy⟩)
      · exact Finset.mem_union_right _ (by simp [hyR])
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (R.filter (fun y => G.Adj a.1 y)) (Finset.univ \ R)
    have h3 : (Finset.univ \ R).card = 2*k := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    have h4 := G.minDegree_le_degree a.1
    rw [card_neighborFinset_eq_degree] at h1
    have hgt : 1 < (R.filter (fun y => G.Adj a.1 y)).card := by omega
    obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Finset.one_lt_card.mp hgt
    rw [Finset.mem_filter] at hy1 hy2
    have hn1 : e ⟨y1, hy1.1⟩ ∈ H.neighborFinset x := by
      rw [mem_neighborFinset, hHadj, Equiv.symm_apply_apply]
      exact hy1.2
    have hn2 : e ⟨y2, hy2.1⟩ ∈ H.neighborFinset x := by
      rw [mem_neighborFinset, hHadj, Equiv.symm_apply_apply]
      exact hy2.2
    have hne : e ⟨y1, hy1.1⟩ ≠ e ⟨y2, hy2.1⟩ := by
      intro h
      exact hy12 (congrArg Subtype.val (e.injective h))
    have := Finset.card_le_card (show {e ⟨y1, hy1.1⟩, e ⟨y2, hy2.1⟩} ⊆ H.neighborFinset x by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hn1
      · exact hn2)
    rw [Finset.card_pair hne, card_neighborFinset_eq_degree] at this
    exact this
  have hmaxH : ∀ x, (Hᶜ).degree x ≤ 2*j-3 := by
    intro x
    have h1 := H.degree_compl x
    rw [Fintype.card_fin] at h1
    have := hdegH x
    omega
  have heu : (e.symm (e u')).1 = u := by rw [Equiv.symm_apply_apply]
  have htriH : ∀ a b, (Hᶜ).Adj (e u') a → (Hᶜ).Adj (e u') b → a ≠ b → ¬ (Hᶜ).Adj a b := by
    intro a b ha hb hab
    rw [hHc, heu] at ha hb
    rw [hHc]
    exact htri _ _ ha hb (fun h => hab (e.symm.injective (Subtype.ext h)))
  have hsquareH : ∀ a b x, (Hᶜ).Adj (e u') a → (Hᶜ).Adj (e u') b → a ≠ b → x ≠ e u' →
      ¬ ((Hᶜ).Adj a x ∧ (Hᶜ).Adj b x) := by
    intro a b x ha hb hab hx
    rw [hHc, heu] at ha hb
    rw [hHc, hHc]
    refine hsquare _ _ _ ha hb (fun h => hab (e.symm.injective (Subtype.ext h))) ?_
    intro h
    apply hx
    rw [← heu] at h
    have := e.symm.injective (Subtype.ext h)
    exact this
  rcases matching_short_switch_complement_local_girth_five j hj H (P.comap f1) hPH hdegH hmaxH
      (e u') (e v') huvH htriH hsquareH with h4 | h6
  · exact hblock.1 h4
  · exact hblock.2 h6
