import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.MatchingShortAlternatingCycleNearUniversal
import AFTD.Kb.Tcs.MatchingBlockedShortSwitchesTwoMissingSaturation
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.ForcedMatchingEdgeBlocksFourAndSixSwitches
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.C
import AFTD.Kb.Tcs.Vertices

/-!
# minimally_k_extendable_complement_degree_two_bound

Topic: graphs   Node: de9b9dd3cc81

Provenance: helper lemma. OP-1957: complement degree-two saturation and edge-selection reduction; experiments 34523 and 34555.

For a minimally k-extendable graph on 2k+2j vertices with 2≤j≤k, if some vertex has at most two nonneighbors, then the minimum degree is at most 2k+1.
-/

theorem in1173_pm_comap {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G →g G') (hf : Function.Bijective f) (Q : G'.Subgraph) (hQ : Q.IsPerfectMatching)
    (hadj : ∀ a b, Q.Adj (f a) (f b) → G.Adj a b) : (Q.comap f).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hQ ⊢
  intro a
  obtain ⟨w, hw, hu⟩ := hQ (f a)
  obtain ⟨b, rfl⟩ := hf.2 w
  refine ⟨b, ⟨hadj a b hw, hw⟩, ?_⟩
  intro c hc
  exact hf.1 (hu _ hc.2)

/-- The forced residual of an essential edge, copied onto `Fin (2*j)`. -/
theorem in1173_residual (k j : ℕ) (G : SimpleGraph (Fin (2*k+2*j))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (hdeg : 2*k+2 ≤ G.minDegree)
    (u v : Fin (2*k+2*j)) (huv : G.Adj u v) :
    ∃ (H : SimpleGraph (Fin (2*j))) (φ : Fin (2*j) → Fin (2*k+2*j)) (P : H.Subgraph)
      (uH vH : Fin (2*j)),
      Function.Injective φ ∧ (∀ x y, H.Adj x y ↔ G.Adj (φ x) (φ y)) ∧ P.IsPerfectMatching ∧
      φ uH = u ∧ φ vH = v ∧ P.Adj uH vH ∧
      (∀ x, ∃ a b, a ≠ b ∧ H.Adj x a ∧ H.Adj x b) ∧
      (¬ ∃ a b, Function.Injective (![uH,vH,a,b] : Fin 4 → Fin (2*j)) ∧ P.Adj a b ∧
        H.Adj vH a ∧ H.Adj uH b) ∧
      (¬ ∃ a b c d, Function.Injective (![uH,vH,a,b,c,d] : Fin 6 → Fin (2*j)) ∧ P.Adj a b ∧
        P.Adj c d ∧ H.Adj vH b ∧ H.Adj a c ∧ H.Adj uH d) := open SimpleGraph in by
  classical
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
  let f1 : H →g GR := ⟨e.symm, fun h => h⟩
  have hPH : (P.comap f1).IsPerfectMatching :=
    in1173_pm_comap f1 e.symm.bijective P hP (fun a b h => P.adj_sub h)
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
    refine ⟨Q.comap f2, in1173_pm_comap f2 e.bijective Q hQ ?_⟩
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
  have hdegH : ∀ x, ∃ a b, a ≠ b ∧ H.Adj x a ∧ H.Adj x b := by
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
    refine ⟨e ⟨y1, hy1.1⟩, e ⟨y2, hy2.1⟩, ?_, ?_, ?_⟩
    · intro h
      exact hy12 (congrArg Subtype.val (e.injective h))
    · rw [hHadj, Equiv.symm_apply_apply]; exact hy1.2
    · rw [hHadj, Equiv.symm_apply_apply]; exact hy2.2
  refine ⟨H, fun x => (e.symm x).1, P.comap f1, e u', e v', ?_, hHadj, hPH, ?_, ?_, huvH,
    hdegH, hblock.1, hblock.2⟩
  · intro x y h
    exact e.symm.injective (Subtype.ext h)
  · show (e.symm (e u')).1 = u
    rw [Equiv.symm_apply_apply]
  · show (e.symm (e v')).1 = v
    rw [Equiv.symm_apply_apply]

/-- One essential edge `uv` with `v` adjacent to both nonneighbours `a,b` of `u`. -/
theorem in1173_claim (k j : ℕ) (G : SimpleGraph (Fin (2*k+2*j))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (hdeg : 2*k+2 ≤ G.minDegree)
    (hH : ∀ x, (Gᶜ).degree x ≤ 2*j-3)
    (u a b v : Fin (2*k+2*j)) (hab : a ≠ b)
    (hNu : ∀ x, (Gᶜ).Adj u x ↔ x = a ∨ x = b)
    (huv : G.Adj u v) (hva : G.Adj v a) (hvb : G.Adj v b) :
    (∃ x, (Gᶜ).Adj a x ∧ x ≠ u) ∧ ∀ x, (Gᶜ).Adj a x → x ≠ u → (Gᶜ).Adj v x ∧ (Gᶜ).Adj b x :=
    open SimpleGraph in by
  classical
  obtain ⟨H, φ, P, uH, vH, hφ, hHadj, hP, huH, hvH, hPuv, hdegH, h4, h6⟩ :=
    in1173_residual k j G hmin hdeg u v huv
  have hHc : ∀ x y, (Hᶜ).Adj x y ↔ (Gᶜ).Adj (φ x) (φ y) := by
    intro x y
    rw [compl_adj, compl_adj, hHadj]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun h => h1 (hφ h), h2⟩, fun ⟨h1, h2⟩ => ⟨fun h => h1 (h ▸ rfl), h2⟩⟩
  -- u has two non-neighbours in H
  have hnear : ¬ ∀ a b, a ≠ uH → b ≠ uH → ¬ H.Adj uH a → ¬ H.Adj uH b → a = b := by
    intro hn
    rcases matching_short_alternating_cycle_near_universal H P hP hdegH uH vH hPuv hn with h | h
    · exact h4 h
    · exact h6 h
  push Not at hnear
  obtain ⟨a1, b1, ha1u, hb1u, hna1, hnb1, ha1b1⟩ := hnear
  have hca1 : (Gᶜ).Adj u (φ a1) := by
    rw [← huH, ← hHc, compl_adj]; exact ⟨fun h => ha1u h.symm, hna1⟩
  have hcb1 : (Gᶜ).Adj u (φ b1) := by
    rw [← huH, ← hHc, compl_adj]; exact ⟨fun h => hb1u h.symm, hnb1⟩
  have hφab : φ a1 ≠ φ b1 := fun h => ha1b1 (hφ h)
  obtain ⟨aH, bH, haH, hbH, haHu, hbHu, hnaH, hnbH⟩ :
      ∃ aH bH, φ aH = a ∧ φ bH = b ∧ aH ≠ uH ∧ bH ≠ uH ∧ ¬ H.Adj uH aH ∧ ¬ H.Adj uH bH := by
    rcases (hNu _).1 hca1 with h1 | h1 <;> rcases (hNu _).1 hcb1 with h2 | h2
    · exact absurd (h1.trans h2.symm) hφab
    · exact ⟨a1, b1, h1, h2, ha1u, hb1u, hna1, hnb1⟩
    · exact ⟨b1, a1, h2, h1, hb1u, ha1u, hnb1, hna1⟩
    · exact absurd (h1.trans h2.symm) hφab
  have habH : aH ≠ bH := fun h => hab (by rw [← haH, ← hbH, h])
  have hvaH : H.Adj vH aH := by rw [hHadj, hvH, haH]; exact hva
  have hvbH : H.Adj vH bH := by rw [hHadj, hvH, hbH]; exact hvb
  have honly : ∀ x, x ≠ uH → ¬ H.Adj uH x → x = aH ∨ x = bH := by
    intro x hx hnx
    have : (Gᶜ).Adj u (φ x) := by
      rw [← huH, ← hHc, compl_adj]; exact ⟨fun h => hx h.symm, hnx⟩
    rcases (hNu _).1 this with h | h
    · left; exact hφ (h.trans haH.symm)
    · right; exact hφ (h.trans hbH.symm)
  have hsep : ∀ x, x ≠ uH → ¬ H.Adj uH x → H.Adj vH x := by
    intro x hx hnx
    rcases honly x hx hnx with rfl | rfl
    · exact hvaH
    · exact hvbH
  have h4' : ∀ x y, Function.Injective (![uH,vH,x,y] : Fin 4 → Fin (2*j)) → P.Adj x y →
      ¬ (H.Adj vH x ∧ H.Adj uH y) := fun x y hi hp hh => h4 ⟨x, y, hi, hp, hh.1, hh.2⟩
  have h6' : ∀ x y z w, Function.Injective (![uH,vH,x,y,z,w] : Fin 6 → Fin (2*j)) →
      P.Adj x y → P.Adj z w → ¬ (H.Adj vH y ∧ H.Adj x z ∧ H.Adj uH w) :=
    fun x y z w hi hp hq hh => h6 ⟨x, y, z, w, hi, hp, hq, hh.1, hh.2.1, hh.2.2⟩
  obtain ⟨-, hsat⟩ := matching_blocked_short_switches_two_missing_saturation H P hP uH vH aH bH
    hPuv habH haHu hbHu hnaH hnbH honly hsep h4' h6'
  have huvH : uH ≠ vH := (P.adj_sub hPuv).ne
  have hvaH' : vH ≠ aH := hvaH.ne
  have hvbH' : vH ≠ bH := hvbH.ne
  -- the vertices of H other than uH, vH, aH, bH
  set D := Finset.univ \ ({uH, vH, aH, bH} : Finset (Fin (2*j))) with hD
  have hmemD : ∀ x, x ∈ D ↔ x ≠ uH ∧ x ≠ vH ∧ x ≠ aH ∧ x ≠ bH := by
    intro x; simp [hD]
  have h4c : ({uH, vH, aH, bH} : Finset (Fin (2*j))).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [huvH, haHu.symm, hbHu.symm]),
      Finset.card_insert_of_notMem (by simp [hvaH', hvbH']),
      Finset.card_pair habH]
  have hDc : D.card + 4 = 2*j := by
    rw [hD, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, h4c]
    have : 4 ≤ 2*j := by
      have := Finset.card_le_univ ({uH, vH, aH, bH} : Finset (Fin (2*j)))
      rw [Fintype.card_fin, h4c] at this
      exact this
    omega
  -- D is nonempty, else u has at most one neighbour in H
  have hDne : D.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    have hD0 : D.card = 0 := by omega
    obtain ⟨x, y, hxy, hx, hy⟩ := hdegH uH
    have hx' : x = vH := by
      by_contra hxv
      have : x ∈ D := (hmemD x).2 ⟨hx.ne.symm, hxv,
        fun h => hnaH (h ▸ hx), fun h => hnbH (h ▸ hx)⟩
      rw [Finset.card_eq_zero] at hD0
      simp [hD0] at this
    have hy' : y = vH := by
      by_contra hyv
      have : y ∈ D := (hmemD y).2 ⟨hy.ne.symm, hyv,
        fun h => hnaH (h ▸ hy), fun h => hnbH (h ▸ hy)⟩
      rw [Finset.card_eq_zero] at hD0
      simp [hD0] at this
    exact hxy (hx'.trans hy'.symm)
  have hDa : ∀ x ∈ D, (Gᶜ).Adj a (φ x) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := (hmemD x).1 hx
    rw [← haH, ← hHc, compl_adj]
    exact ⟨fun h => h3 h.symm, (hsat x h1 h2 h3 h4).2.1⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hDne
    refine ⟨φ x, hDa x hx, ?_⟩
    rw [← huH]
    exact fun h => ((hmemD x).1 hx).1 (hφ h)
  · -- the complement neighbourhood of a is u together with φ(D)
    have hsub : insert u (D.image φ) ⊆ (Gᶜ).neighborFinset a := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_image] at hy
      rw [mem_neighborFinset]
      rcases hy with rfl | ⟨x, hx, rfl⟩
      · exact ((hNu a).2 (Or.inl rfl)).symm
      · exact hDa x hx
    have hcard : (insert u (D.image φ)).card = 2*j-3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hφ]
      · omega
      · rw [Finset.mem_image]
        rintro ⟨x, hx, hxu⟩
        rw [← huH] at hxu
        exact ((hmemD x).1 hx).1 (hφ hxu)
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [card_neighborFinset_eq_degree, hcard]; exact hH a)
    intro y hy hyu
    have hy' : y ∈ insert u (D.image φ) := by rw [heq, mem_neighborFinset]; exact hy
    rw [Finset.mem_insert, Finset.mem_image] at hy'
    rcases hy' with rfl | ⟨x, hx, rfl⟩
    · exact absurd rfl hyu
    · obtain ⟨h1, h2, h3, h4⟩ := (hmemD x).1 hx
      have hs := hsat x h1 h2 h3 h4
      refine ⟨?_, ?_⟩
      · rw [← hvH, ← hHc, compl_adj]; exact ⟨fun h => h2 h.symm, hs.1⟩
      · rw [← hbH, ← hHc, compl_adj]; exact ⟨fun h => h4 h.symm, hs.2.2⟩

theorem minimally_k_extendable_complement_degree_two_bound
    (k j : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k)
    (G : SimpleGraph (Fin (2*k+2*j))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (u : Fin (2*k+2*j))
    (hu : (Gᶜ).degree u ≤ 2) : G.minDegree ≤ 2*k+1 := open SimpleGraph in by
  classical
  by_contra hlt
  have hdeg : 2*k+2 ≤ G.minDegree := by omega
  have hH : ∀ x, (Gᶜ).degree x ≤ 2*j-3 := by
    intro x
    have h1 := G.degree_compl x
    have h2 := G.minDegree_le_degree x
    rw [Fintype.card_fin] at h1
    omega
  by_cases h2 : (Gᶜ).degree u = 2
  · rw [← card_neighborFinset_eq_degree] at h2
    obtain ⟨a, b, hab, hNab⟩ := Finset.card_eq_two.mp h2
    have hNu : ∀ x, (Gᶜ).Adj u x ↔ x = a ∨ x = b := by
      intro x
      rw [← mem_neighborFinset, hNab]
      simp
    have hua : (Gᶜ).Adj u a := (hNu a).2 (Or.inl rfl)
    have hub : (Gᶜ).Adj u b := (hNu b).2 (Or.inr rfl)
    -- X: common graph neighbours of u, a, b
    set X := Finset.univ.filter (fun v => G.Adj u v ∧ G.Adj v a ∧ G.Adj v b) with hX
    have hXc : Finset.univ \ X ⊆ insert u ((Gᶜ).neighborFinset u ∪ (Gᶜ).neighborFinset a ∪
        (Gᶜ).neighborFinset b) := by
      intro v hv
      simp only [hX, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hv
      simp only [Finset.mem_insert, Finset.mem_union, mem_neighborFinset, compl_adj]
      by_cases hvu : v = u
      · exact Or.inl hvu
      by_cases hva : v = a
      · exact Or.inr (Or.inl (Or.inl (hva ▸ (compl_adj G u a).1 hua)))
      by_cases hvb : v = b
      · exact Or.inr (Or.inl (Or.inl (hvb ▸ (compl_adj G u b).1 hub)))
      by_cases h1 : G.Adj u v
      · by_cases h2 : G.Adj v a
        · exact Or.inr (Or.inr ⟨fun h => hvb h.symm, fun h => hv ⟨h1, h2, h.symm⟩⟩)
        · exact Or.inr (Or.inl (Or.inr ⟨fun h => hva h.symm, fun h => h2 h.symm⟩))
      · exact Or.inr (Or.inl (Or.inl ⟨fun h => hvu h.symm, h1⟩))
    have hXpos : 0 < X.card := by
      have c1 := Finset.card_le_card hXc
      have c2 := Finset.card_insert_le u ((Gᶜ).neighborFinset u ∪ (Gᶜ).neighborFinset a ∪
        (Gᶜ).neighborFinset b)
      have c3 := Finset.card_union_le ((Gᶜ).neighborFinset u ∪ (Gᶜ).neighborFinset a)
        ((Gᶜ).neighborFinset b)
      have c4 := Finset.card_union_le ((Gᶜ).neighborFinset u) ((Gᶜ).neighborFinset a)
      rw [card_neighborFinset_eq_degree] at c3 c4
      rw [card_neighborFinset_eq_degree] at c4
      have c5 : (Finset.univ \ X).card + X.card = 2*k+2*j := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        have := Finset.card_le_univ X
        rw [Fintype.card_fin] at this
        omega
      have := hH a
      have := hH b
      have : (Gᶜ).degree u = 2 := by rw [← card_neighborFinset_eq_degree]; exact h2
      omega
    obtain ⟨v0, hv0⟩ := Finset.card_pos.mp hXpos
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hv0
    obtain ⟨⟨x0, hax0, hx0u⟩, -⟩ :=
      in1173_claim k j G hmin hdeg hH u a b v0 hab hNu hv0.1 hv0.2.1 hv0.2.2
    have hba := (in1173_claim k j G hmin hdeg hH u b a v0 hab.symm
      (fun x => by rw [hNu]; tauto) hv0.1 hv0.2.2 hv0.2.1).2
    -- every vertex outside {u,a,b} ∪ N̄(a) is a complement neighbour of x0
    set T := insert u (insert a (insert b ((Gᶜ).neighborFinset a))) with hT
    have hsub : Finset.univ \ T ⊆ (Gᶜ).neighborFinset x0 := by
      intro y hy
      simp only [hT, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, mem_neighborFinset,
        true_and, not_or] at hy
      obtain ⟨hyu, hya, hyb, hay⟩ := hy
      have h1 : G.Adj u y := by
        by_contra h
        rcases (hNu y).1 ((compl_adj G u y).2 ⟨fun e => hyu e.symm, h⟩) with e | e
        · exact hya e
        · exact hyb e
      have h2 : G.Adj y a := by
        by_contra h
        exact hay ((compl_adj G a y).2 ⟨fun e => hya e.symm, fun e => h e.symm⟩)
      have h3 : G.Adj y b := by
        by_contra h
        have hby : (Gᶜ).Adj b y := (compl_adj G b y).2 ⟨fun e => hyb e.symm, fun e => h e.symm⟩
        exact hay (hba y hby hyu).2
      have hc := (in1173_claim k j G hmin hdeg hH u a b y hab hNu h1 h2 h3).2 x0 hax0 hx0u
      rw [mem_neighborFinset]
      exact hc.1.symm
    have c1 := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree] at c1
    have c2 : T.card ≤ 2*j := by
      rw [hT]
      have e1 := Finset.card_insert_le u (insert a (insert b ((Gᶜ).neighborFinset a)))
      have e2 := Finset.card_insert_le a (insert b ((Gᶜ).neighborFinset a))
      have e3 := Finset.card_insert_le b ((Gᶜ).neighborFinset a)
      rw [card_neighborFinset_eq_degree] at e3
      have := hH a
      have hj3 : 3 ≤ 2*j := by omega
      omega
    have c3 : (Finset.univ \ T).card + T.card = 2*k+2*j := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have := Finset.card_le_univ T
      rw [Fintype.card_fin] at this
      omega
    have := hH x0
    omega
  · -- at most one nonneighbour: the near-universal switch
    have hle1 : (Gᶜ).degree u ≤ 1 := by omega
    obtain ⟨v, huv⟩ : ∃ v, G.Adj u v := by
      have h := G.minDegree_le_degree u
      have : 0 < (G.neighborFinset u).card := by rw [card_neighborFinset_eq_degree]; omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp this
      exact ⟨v, (mem_neighborFinset _ _ _).1 hv⟩
    obtain ⟨H, φ, P, uH, vH, hφ, hHadj, hP, huH, hvH, hPuv, hdegH, h4, h6⟩ :=
      in1173_residual k j G hmin hdeg u v huv
    have hnear : ∀ a b, a ≠ uH → b ≠ uH → ¬ H.Adj uH a → ¬ H.Adj uH b → a = b := by
      intro a b ha hb hna hnb
      have hca : φ a ∈ (Gᶜ).neighborFinset u := by
        rw [mem_neighborFinset, compl_adj, ← huH, ← hHadj]
        exact ⟨fun h => ha (hφ h).symm, hna⟩
      have hcb : φ b ∈ (Gᶜ).neighborFinset u := by
        rw [mem_neighborFinset, compl_adj, ← huH, ← hHadj]
        exact ⟨fun h => hb (hφ h).symm, hnb⟩
      have : ((Gᶜ).neighborFinset u).card ≤ 1 := by rw [card_neighborFinset_eq_degree]; exact hle1
      exact hφ (Finset.card_le_one.mp this _ hca _ hcb)
    rcases matching_short_alternating_cycle_near_universal H P hP hdegH uH vH hPuv hnear with h | h
    · exact h4 h
    · exact h6 h
