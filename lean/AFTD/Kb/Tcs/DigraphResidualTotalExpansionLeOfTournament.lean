import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphClosedOutNbr
import AFTD.Kb.Tcs.DigraphExpansion
import AFTD.Kb.Tcs.DigraphIsExtension
import AFTD.Kb.Tcs.DigraphResidualAt
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphIsOriented
import AFTD.Kb.Tcs.DigraphResidualSubsetOutNbr
import AFTD.Kb.Tcs.DigraphResidualContainsSelf
import AFTD.Kb.Tcs.DigraphOutBoundary

/-!
# digraph_residual_total_expansion_le_of_tournament

Topic: graphs   Node: 180087df33ea

Provenance: formalization of a published result. Source: arXiv:2611.32872 Lemma 2

For a finite type V with decidable equality and directed graphs G and H of type Digraph V with decidable adjacency relations, if G is oriented (digraph_is_oriented G), H is an extension of G (digraph_is_extension G H), and H is a tournament (digraph_is_tournament H), then the sum over all vertices v : V of digraph_expansion G (digraph_residual_at G H v) is at most the sum over all vertices v : V of digraph_expansion G (digraph_closed_out_nbr H {v}).
-/

theorem digraph_residual_total_expansion_le_of_tournament_mem_digraph_out_boundary_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (X : Finset V) (y : V) :
    y ∈ digraph_out_boundary G X ↔ y ∉ X ∧ ∃ x ∈ X, G.Adj x y := by
  simp only [digraph_out_boundary, digraph_closed_out_nbr, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨h1 | ⟨x, hx, hadj⟩, h2⟩
    · exact (h2 h1).elim
    · exact ⟨h2, x, hx, hadj⟩
  · rintro ⟨h2, x, hx, hadj⟩
    exact ⟨Or.inr ⟨x, hx, hadj⟩, h2⟩

theorem digraph_residual_total_expansion_le_of_tournament_mem_digraph_closed_out_nbr_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (H : Digraph V) [DecidableRel H.Adj] (v y : V) :
    y ∈ digraph_closed_out_nbr H {v} ↔ y = v ∨ H.Adj v y := by
  simp only [digraph_closed_out_nbr, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨x, rfl, hadj⟩)
    · left; rfl
    · right; exact hadj
  · rintro (rfl | hadj)
    · left; rfl
    · right; exact ⟨v, rfl, hadj⟩

theorem digraph_residual_total_expansion_le_of_tournament_no_collision_helper {V : Type*} [Fintype V] [DecidableEq V]
    (G H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hH_ext : digraph_is_extension G H)
    (hH_tourn : digraph_is_tournament H)
    (a b : V)
    (ha : b ∈ digraph_out_boundary G (digraph_residual_at G H a))
    (hb : a ∈ digraph_out_boundary G (digraph_residual_at G H b)) :
    False := by
  have hGH : G ≤ H := hH_ext.2
  have hH_or : digraph_is_oriented H := hH_ext.1
  simp only [digraph_out_boundary, digraph_closed_out_nbr, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha hb
  rcases ha with ⟨h1a | ⟨x, hx_Ra, hxb⟩, hnb_Ra⟩
  · exact (hnb_Ra h1a).elim
  rcases hb with ⟨h1b | ⟨z, hz_Rb, hza⟩, hna_Rb⟩
  · exact (hna_Rb h1b).elim
  have hx_spec : ∀ u, u = a ∨ G.Adj u a → u = x ∨ H.Adj u x := by
    simp only [digraph_residual_at, Finset.mem_filter, Finset.mem_univ, true_and] at hx_Ra
    exact hx_Ra
  have hz_spec : ∀ u, u = b ∨ G.Adj u b → u = z ∨ H.Adj u z := by
    simp only [digraph_residual_at, Finset.mem_filter, Finset.mem_univ, true_and] at hz_Rb
    exact hz_Rb
  have hzx_or := hx_spec z (Or.inr hza)
  have hxz_or := hz_spec x (Or.inr hxb)
  by_cases hzx : z = x
  · have hHxa : H.Adj x a := by
      rw [← hzx]
      exact hGH hza
    have hx_Ha : x ∈ digraph_closed_out_nbr H {a} :=
      digraph_residual_subset_out_nbr G H a hx_Ra
    simp only [digraph_closed_out_nbr, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and] at hx_Ha
    rcases hx_Ha with rfl | ⟨_, rfl, hHax⟩
    · exact hH_tourn.1 _ hHxa
    · exact hH_or _ _ hHxa hHax
  · rcases hzx_or with rfl | hHzx
    · exact (hzx rfl).elim
    · rcases hxz_or with rfl | hHxz
      · exact (hzx rfl.symm).elim
      · exact hH_or z x hHzx hHxz

theorem digraph_residual_total_expansion_le_of_tournament_maps_to_helper {V : Type*} [Fintype V] [DecidableEq V]
    (G H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hH_ext : digraph_is_extension G H)
    (hH_tourn : digraph_is_tournament H)
    (v y : V)
    (hy : y ∈ digraph_out_boundary G (digraph_residual_at G H v)) :
    if H.Adj y v then
      y ∈ digraph_out_boundary G (digraph_closed_out_nbr H {v})
    else
      v ∈ digraph_out_boundary G (digraph_closed_out_nbr H {y}) := by
  have hH_or : digraph_is_oriented H := hH_ext.1
  have hGH : G ≤ H := hH_ext.2
  rw [digraph_residual_total_expansion_le_of_tournament_mem_digraph_out_boundary_iff] at hy
  rcases hy with ⟨hny_Rv, x, hx_Rv, hxy⟩
  have hv_Rv : v ∈ digraph_residual_at G H v := digraph_residual_contains_self G H hGH v
  have hvy : v ≠ y := by
    rintro rfl
    exact hny_Rv hv_Rv
  split_ifs with hHyv
  · -- Case 1: H.Adj y v
    rw [digraph_residual_total_expansion_le_of_tournament_mem_digraph_out_boundary_iff]
    refine ⟨?_, x, digraph_residual_subset_out_nbr G H v hx_Rv, hxy⟩
    rw [digraph_residual_total_expansion_le_of_tournament_mem_digraph_closed_out_nbr_singleton]
    rintro (rfl | hHvy)
    · exact hH_tourn.1 _ hHyv
    · exact hH_or y v hHyv hHvy
  · -- Case 2: ¬ H.Adj y v
    have hHvy : H.Adj v y := by
      have ht := hH_tourn.2 v y hvy
      tauto
    simp only [digraph_residual_at, Finset.mem_filter, Finset.mem_univ, true_and] at hny_Rv
    have h_ex : ∃ u, (u = v ∨ G.Adj u v) ∧ u ≠ y ∧ ¬ H.Adj u y := by
      by_contra hc
      apply hny_Rv
      intro u hu
      by_contra hc2
      push Not at hc2
      exact hc ⟨u, hu, hc2⟩
    rcases h_ex with ⟨u, hu_in, huy, hHuy⟩
    rcases hu_in with rfl | hGuv
    · exact (hHuy hHvy).elim
    have hHyu : H.Adj y u := by
      have ht := hH_tourn.2 y u (Ne.symm huy)
      tauto
    rw [digraph_residual_total_expansion_le_of_tournament_mem_digraph_out_boundary_iff]
    refine ⟨?_, u, ?_, hGuv⟩
    · rw [digraph_residual_total_expansion_le_of_tournament_mem_digraph_closed_out_nbr_singleton]
      rintro (rfl | hHyv')
      · exact hvy rfl
      · exact hHyv hHyv'
    · rw [digraph_residual_total_expansion_le_of_tournament_mem_digraph_closed_out_nbr_singleton]
      right
      exact hHyu

theorem digraph_residual_total_expansion_le_of_tournament_card_filter_prod_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (F : V → Finset V) :
    ∑ v : V, (F v).card = ((Finset.univ : Finset (V × V)).filter (fun p => p.2 ∈ F p.1)).card := by
  rw [Finset.card_filter]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.card_filter]
  congr 1
  ext v
  congr 1
  ext y
  simp

/-- Residual Total Expansion Bound for Tournament Extensions of Oriented Graphs (Lemma 2). -/
theorem digraph_residual_total_expansion_le_of_tournament {V : Type*} [Fintype V] [DecidableEq V]
    (G H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : digraph_is_oriented G) (hH_ext : digraph_is_extension G H)
    (hH_tourn : digraph_is_tournament H) :
    ∑ v : V, digraph_expansion G (digraph_residual_at G H v) ≤
      ∑ v : V, digraph_expansion G (digraph_closed_out_nbr H {v}) := by
  unfold digraph_expansion
  rw [digraph_residual_total_expansion_le_of_tournament_card_filter_prod_eq_sum,
      digraph_residual_total_expansion_le_of_tournament_card_filter_prod_eq_sum]
  let s : Finset (V × V) := (Finset.univ : Finset (V × V)).filter (fun p => p.2 ∈ digraph_out_boundary G (digraph_residual_at G H p.1))
  let t : Finset (V × V) := (Finset.univ : Finset (V × V)).filter (fun p => p.2 ∈ digraph_out_boundary G (digraph_closed_out_nbr H {p.1}))
  let f : (V × V) → (V × V) := fun (v, y) => if H.Adj y v then (v, y) else (y, v)
  have h_maps : Set.MapsTo f ↑s ↑t := by
    rintro ⟨v, y⟩ hp
    simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [f]
    have hm := digraph_residual_total_expansion_le_of_tournament_maps_to_helper G H hH_ext hH_tourn v y hp
    split_ifs with hHyv
    · simp only [t, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_pos hHyv] at hm
      exact hm
    · simp only [t, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_neg hHyv] at hm
      exact hm
  have h_inj : Set.InjOn f ↑s := by
    rintro ⟨v1, y1⟩ hp1 ⟨v2, y2⟩ hp2 heq
    simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    simp only [f] at heq
    split_ifs at heq with h1 h2
    · injection heq with hv hy
      rw [hv, hy]
    · injection heq with hv hy
      have h_False := digraph_residual_total_expansion_le_of_tournament_no_collision_helper G H hH_ext hH_tourn v1 y1 hp1 (by
        rw [hv, hy]
        exact hp2)
      exact h_False.elim
    · injection heq with hv hy
      have h_False := digraph_residual_total_expansion_le_of_tournament_no_collision_helper G H hH_ext hH_tourn v2 y2 hp2 (by
        rw [← hv, ← hy]
        exact hp1)
      exact h_False.elim
    · injection heq with hv hy
      rw [hv, hy]
  exact Finset.card_le_card_of_injOn f h_maps h_inj
