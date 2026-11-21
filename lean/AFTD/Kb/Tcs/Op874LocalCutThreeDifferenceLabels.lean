import AFTD.Prelude

/-!
# op874_local_cut_three_difference_labels

Topic: graphs   Node: be83bd110a42

Provenance: helper lemma. OP-874: three labels on matching edges and same-bit factor edges of a locally maximal cut

For a simple cubic graph and a locally maximal cut constant on perfect-matching pairs, its vertices admit three labels that differ across every matching edge and every same-bit factor edge.
-/

lemma op874_local_cut_three_difference_labels_mate_unique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hsub : M ⊆ G.edgeFinset)
    (hperfect : ∀ v : V, ∃! e : Sym2 V, e ∈ M ∧ v ∈ e) (v : V) :
    ∃! u : V, s(v, u) ∈ M := by
  obtain ⟨e, ⟨heM, hve⟩, heuniq⟩ := hperfect v
  have he_adj : e ∈ G.edgeFinset := hsub heM
  rw [SimpleGraph.mem_edgeFinset] at he_adj
  obtain ⟨⟨x, z⟩, rfl⟩ := Quot.exists_rep e
  rw [Sym2.mem_iff] at hve
  have hne : x ≠ z := G.ne_of_adj he_adj
  cases hve with
  | inl hvx =>
    subst hvx
    refine ⟨z, heM, ?_⟩
    intro u hu
    have hu_in : v ∈ s(v, u) := Sym2.mem_mk_left v u
    have h_eq := heuniq s(v, u) ⟨hu, hu_in⟩
    rw [Sym2.eq_iff] at h_eq
    rcases h_eq with (⟨_, rfl⟩ | ⟨rfl, _⟩)
    · rfl
    · exact (hne rfl).elim
  | inr hvz =>
    subst hvz
    have heM' : s(v, x) ∈ M := by rwa [Sym2.eq_swap]
    refine ⟨x, heM', ?_⟩
    intro u hu
    have hu_in : v ∈ s(v, u) := Sym2.mem_mk_left v u
    have h_eq := heuniq s(v, u) ⟨hu, hu_in⟩
    rw [Sym2.eq_iff] at h_eq
    rcases h_eq with (⟨rfl, _⟩ | ⟨_, rfl⟩)
    · exact (hne.symm rfl).elim
    · rfl

lemma op874_local_cut_three_difference_labels_deg_lt_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : G.IsRegularOfDegree 3)
    (M : Finset (Sym2 V)) (hsub : M ⊆ G.edgeFinset)
    (hperfect : ∀ v : V, ∃! e : Sym2 V, e ∈ M ∧ v ∈ e)
    (b : V → Bool)
    (hcut : ∀ u v, G.Adj u v → s(u,v) ∈ M →
      ((G.neighborFinset u).filter fun w => b w = b u ∧ s(u,w) ∉ M).card +
      ((G.neighborFinset v).filter fun w => b w = b v ∧ s(v,w) ∉ M).card ≤ 2)
    (s : Finset V) (hs : s.Nonempty) :
    ∃ v ∈ s, (s.filter fun w => G.Adj v w ∧ (s(v,w) ∈ M ∨ b v = b w)).card < 3 := by
  let R := fun u v => G.Adj u v ∧ (s(u,v) ∈ M ∨ b u = b v)
  change ∃ v ∈ s, (s.filter (R v)).card < 3
  by_contra! hall
  obtain ⟨u, hu⟩ := hs
  have hcard_u := hall u hu
  have hsub_u : s.filter (R u) ⊆ G.neighborFinset u := by
    intro w hw
    rw [Finset.mem_filter] at hw
    exact (SimpleGraph.mem_neighborFinset G u w).mpr hw.2.1
  have hdeg_u : (G.neighborFinset u).card = 3 := hcubic u
  have heq_u : s.filter (R u) = G.neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le hsub_u
    omega
  obtain ⟨v, hvuM, hvuniq⟩ := op874_local_cut_three_difference_labels_mate_unique G M hsub hperfect u
  have hadj_uv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (hsub hvuM)
  have hvin : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u v).mpr hadj_uv
  have hvs : v ∈ s := by
    have : v ∈ s.filter (R u) := by
      rw [heq_u]
      exact hvin
    exact (Finset.mem_filter.mp this).1
  have hcard_v := hall v hvs
  let Fu := (G.neighborFinset u).filter fun w => b w = b u ∧ s(u,w) ∉ M
  let Fv := (G.neighborFinset v).filter fun w => b w = b v ∧ s(v,w) ∉ M
  have hcut_uv : Fu.card + Fv.card ≤ 2 := hcut u v hadj_uv hvuM
  have hsub_Fu : (G.neighborFinset u).erase v ⊆ Fu := by
    intro w hw
    rw [Finset.mem_erase] at hw
    rw [Finset.mem_filter]
    refine ⟨hw.2, ⟨?_, ?_⟩⟩
    · have hw_in : w ∈ s.filter (R u) := by
        rw [heq_u]
        exact hw.2
      have hw_R := (Finset.mem_filter.mp hw_in).2.2
      rcases hw_R with (hwM | hwb)
      · exfalso
        exact hw.1 (hvuniq w hwM)
      · exact hwb.symm
    · intro hwM
      exact hw.1 (hvuniq w hwM)
  have hcard_Fu : 2 ≤ Fu.card := by
    have h_erase : ((G.neighborFinset u).erase v).card = 2 := by
      rw [Finset.card_erase_of_mem hvin, hdeg_u]
    rw [← h_erase]
    exact Finset.card_le_card hsub_Fu
  have hFv_zero : Fv.card = 0 := by omega
  have hsub_v : s.filter (R v) ⊆ {u} := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_singleton]
    have hw_adj : w ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v w).mpr hw.2.1
    have hvu_swap : s(v, u) ∈ M := by rwa [Sym2.eq_swap]
    obtain ⟨u', hvu'M, hu'uniq⟩ := op874_local_cut_three_difference_labels_mate_unique G M hsub hperfect v
    have hu'_eq : u = u' := hu'uniq u hvu_swap
    by_cases hwM : s(v, w) ∈ M
    · have hw_eq : w = u' := hu'uniq w hwM
      subst hu'_eq hw_eq
      rfl
    · exfalso
      rcases hw.2.2 with (hwM' | hwb)
      · exact hwM hwM'
      · have : w ∈ Fv := by
          rw [Finset.mem_filter]
          exact ⟨hw_adj, ⟨hwb.symm, hwM⟩⟩
        have h_empty : Fv = ∅ := Finset.card_eq_zero.mp hFv_zero
        rw [h_empty] at this
        exact Finset.notMem_empty w this
  have hcard_le_1 : (s.filter (R v)).card ≤ 1 := by
    calc (s.filter (R v)).card ≤ ({u} : Finset V).card := Finset.card_le_card hsub_v
    _ = 1 := Finset.card_singleton u
  omega

lemma op874_local_cut_three_difference_labels_exists_coloring {V : Type*} [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R] (hR : ∀ u v, R u v → R v u)
    (hirr : ∀ v, ¬ R v v)
    (hdeg : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (R v)).card < 3)
    (s : Finset V) :
    ∃ d : V → Fin 3, ∀ u ∈ s, ∀ v ∈ s, R u v → d u ≠ d v := by
  induction' hn : s.card using Nat.strong_induction_on with n ih generalizing s
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv, hcard⟩ := hdeg s hs
    have hlt : (s.erase v).card < n := by
      rw [← hn]
      exact Finset.card_erase_lt_of_mem hv
    obtain ⟨d', hd'⟩ := ih (s.erase v).card hlt (s.erase v) rfl
    let forbidden : Finset (Fin 3) := (s.filter (R v)).image d'
    have hforb : forbidden.card < 3 := by
      calc forbidden.card ≤ (s.filter (R v)).card := Finset.card_image_le
      _ < 3 := hcard
    have hex : ∃ c : Fin 3, c ∉ forbidden := by
      by_contra! hall
      have hle : (Finset.univ : Finset (Fin 3)).card ≤ forbidden.card := by
        apply Finset.card_le_card
        intro x _
        exact hall x
      rw [Finset.card_univ, Fintype.card_fin] at hle
      omega
    obtain ⟨c, hc⟩ := hex
    use fun x => if x = v then c else d' x
    intro u hu w hw hRuw
    dsimp only
    by_cases hu_eq : u = v
    · by_cases hw_eq : w = v
      · rw [hu_eq, hw_eq] at hRuw
        exact (hirr _ hRuw).elim
      · rw [if_pos hu_eq, if_neg hw_eq]
        subst hu_eq
        intro h_eq
        apply hc
        rw [Finset.mem_image]
        refine ⟨w, ?_, h_eq.symm⟩
        rw [Finset.mem_filter]
        exact ⟨hw, hRuw⟩
    · by_cases hw_eq : w = v
      · rw [if_neg hu_eq, if_pos hw_eq]
        subst hw_eq
        intro h_eq
        apply hc
        rw [Finset.mem_image]
        refine ⟨u, ?_, h_eq⟩
        rw [Finset.mem_filter]
        exact ⟨hu, hR u w hRuw⟩
      · rw [if_neg hu_eq, if_neg hw_eq]
        apply hd' u _ w _ hRuw
        · rw [Finset.mem_erase]
          exact ⟨hu_eq, hu⟩
        · rw [Finset.mem_erase]
          exact ⟨hw_eq, hw⟩
  · rw [Finset.nonempty_iff_ne_empty, not_not] at hs
    subst hs
    use fun _ => 0
    intro u hu
    simp at hu

theorem op874_local_cut_three_difference_labels {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : G.IsRegularOfDegree 3) (M : Finset (Sym2 V)) (hsub : M ⊆ G.edgeFinset) (hperfect : ∀ v : V, ∃! e : Sym2 V, e ∈ M ∧ v ∈ e) (b : V → Bool) (hmatching : ∀ u v, G.Adj u v → s(u,v) ∈ M → b u = b v) (hcut : ∀ u v, G.Adj u v → s(u,v) ∈ M → ((G.neighborFinset u).filter fun w => b w = b u ∧ s(u,w) ∉ M).card + ((G.neighborFinset v).filter fun w => b w = b v ∧ s(v,w) ∉ M).card ≤ 2) : ∃ d : V → Fin 3, ∀ u v, G.Adj u v → (s(u,v) ∈ M ∨ b u = b v) → d u ≠ d v := by
  let R := fun u v => G.Adj u v ∧ (s(u,v) ∈ M ∨ b u = b v)
  have hR_symm : ∀ u v, R u v → R v u := by
    intro u v ⟨hadj, hcase⟩
    refine ⟨hadj.symm, ?_⟩
    rcases hcase with (hM | hb)
    · rw [Sym2.eq_swap]
      exact Or.inl hM
    · exact Or.inr hb.symm
  have hR_irr : ∀ v, ¬ R v v := by
    intro v ⟨hadj, _⟩
    exact G.ne_of_adj hadj rfl
  have hdeg : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (R v)).card < 3 := by
    intro s hs
    exact op874_local_cut_three_difference_labels_deg_lt_three G hcubic M hsub hperfect b hcut s hs
  obtain ⟨d, hd⟩ := op874_local_cut_three_difference_labels_exists_coloring R hR_symm hR_irr hdeg Finset.univ
  use d
  intro u v hadj hM_or_b
  exact hd u (Finset.mem_univ u) v (Finset.mem_univ v) ⟨hadj, hM_or_b⟩
