import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyNumber
import AFTD.Kb.Tcs.SupportGraph
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.SetColoringRamseyProperty

/-!
# set_coloring_ramsey_number_triangle_endpoint_le_r_minus_three

Topic: combinatorics   Node: 0541de9309b3

Provenance: formalization of a published result. Source: arXiv:2611.19312 Proposition 1 (iii)

For every integer r ≥ 3 and every 1 ≤ t ≤ r - 3, the set-coloring Ramsey number of the triangle with palette parameters r, r - 1 and intersection parameter t satisfies R(3; r, r-1, t) = 3.
-/

/-- R(3; r, r-1, t) = 3 when 1 ≤ t ≤ r - 3. -/
theorem set_coloring_ramsey_number_triangle_endpoint_le_r_minus_three
    (r t : ℕ) (hr : 3 ≤ r) (ht1 : 1 ≤ t) (ht : t ≤ r - 3) :
    set_coloring_ramsey_number (⊤ : SimpleGraph (Fin 3)) r (r - 1) t = 3 := by
  classical
  have hP3 : set_coloring_ramsey_property (⊤ : SimpleGraph (Fin 3)) r (r - 1) t 3 := by
    intro ϕ hϕ
    let c : (⊤ : SimpleGraph (Fin 3)).edgeSet → Finset (Fin r) := fun e => Finset.univ \ ϕ e
    have hc : ∀ e, (c e).card = 1 := by
      intro e
      show (Finset.univ \ ϕ e).card = 1
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ (ϕ e)), Finset.card_univ, Fintype.card_fin]
      have := hϕ e
      omega
    let B : Finset (Fin r) := Finset.univ.biUnion c
    have hBcard : B.card ≤ 3 := by
      refine le_trans Finset.card_biUnion_le ?_
      rw [Finset.sum_congr rfl (fun e _ => hc e), Finset.sum_const, Finset.card_univ,
        SimpleGraph.card_edgeSet, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp
    have hScard : t ≤ (Finset.univ \ B).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hScard
    have hTϕ : ∀ e, T ⊆ ϕ e := by
      intro e
      have hce : c e ⊆ B := Finset.subset_biUnion_of_mem c (Finset.mem_univ e)
      have h1 : Finset.univ \ B ⊆ Finset.univ \ c e :=
        Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hce
      rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ (ϕ e))] at h1
      exact Finset.Subset.trans hTsub h1
    refine ⟨T, hTcard, ?_⟩
    have hH : support_graph ϕ T = ⊤ := by
      refine le_antisymm le_top ?_
      intro u v huv
      rw [support_graph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨SimpleGraph.mem_edgeSet _ |>.mpr huv, hTϕ _⟩, huv⟩
    rw [hH]
    exact ⟨SimpleGraph.Copy.mk SimpleGraph.Hom.id Function.injective_id⟩
  have hlow : ∀ N, set_coloring_ramsey_property (⊤ : SimpleGraph (Fin 3)) r (r - 1) t N → 3 ≤ N := by
    intro N hN
    have hr0 : 0 < r := by omega
    let ϕ : (⊤ : SimpleGraph (Fin N)).edgeSet → Finset (Fin r) :=
      fun _ => Finset.univ.erase ⟨0, hr0⟩
    have hϕ : ∀ e, (ϕ e).card = r - 1 := by
      intro e
      show (Finset.univ.erase (⟨0, hr0⟩ : Fin r)).card = r - 1
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    obtain ⟨T, hT, hcont⟩ := hN ϕ hϕ
    obtain ⟨cc⟩ := hcont
    have hinj : Function.Injective ⇑cc.toHom := cc.injective'
    have hcard := Fintype.card_le_of_injective (⇑cc.toHom) hinj
    simpa using hcard
  rw [set_coloring_ramsey_number]
  refine le_antisymm (Nat.sInf_le hP3) ?_
  have hmem : sInf {N : ℕ | set_coloring_ramsey_property (⊤ : SimpleGraph (Fin 3)) r (r - 1) t N} ∈
      {N : ℕ | set_coloring_ramsey_property (⊤ : SimpleGraph (Fin 3)) r (r - 1) t N} :=
    Nat.sInf_mem ⟨3, hP3⟩
  exact hlow _ (by simpa using hmem)
