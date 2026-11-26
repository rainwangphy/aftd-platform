import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCrossingAdjacentEndpointsImpossible
import AFTD.Kb.Tcs.MaximumMatchingUncoveredIncidenceIndependenceBound
import AFTD.Kb.Tcs.NoTwoCrossingMatchingIndependenceIncidenceBound
import AFTD.Kb.Tcs.BalancedCutNearPerfectOfIncidenceBounds
import AFTD.Kb.Tcs.MaximumMatchingUnmatchedIndependent
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# extendible_equal_cut_maximum_matching_deficiency_at_most_one

Topic: graphs   Node: 4ac6d486d2a8

Provenance: helper lemma. Balanced-cut reduction for OP-1957; https://arxiv.org/abs/1011.3384.

Under the displayed extendibility, minimum degree, independence and equal-half matching assumptions, a maximum internal matching has at least k−1 edges.
-/

theorem extendible_equal_cut_maximum_matching_deficiency_at_most_one
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching)
    (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hNC : N.verts ⊆ ((C : Set (Fin (4*k)))ᶜ))
    (hmaxM : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin (4*k))) → T.edgeSet.ncard ≤ M.edgeSet.ncard)
    (hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ ((C : Set (Fin (4*k)))ᶜ) → T.edgeSet.ncard ≤ N.edgeSet.ncard)
    (heq : M.edgeSet.ncard = N.edgeSet.ncard)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k) :
    k ≤ M.edgeSet.ncard + 1 := by
  set_option maxHeartbeats 4000000 in
    classical
    let D : Finset (Fin (4*k)) := M.verts.toFinset
    let U : Finset (Fin (4*k)) := C \ D
    let R : Finset (Fin (4*k)) := Cᶜ
    have hDC : D ⊆ C := by intro x hx; exact hMC (by simpa [D] using hx)
    have hUC : U ⊆ C := Finset.sdiff_subset
    have hUn : ∀ x ∈ U, x ∉ M.verts := by
      intro x hx
      have hx' := (Finset.mem_sdiff.mp hx).2
      simpa [D] using hx'
    have hUind : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ¬ G.Adj x y := by
      intro x hx y hy hne
      exact maximum_matching_unmatched_independent G C M hM hMC hmaxM x (hUC hx) (hUn x hx) y (hUC hy) (hUn y hy)
    have hindU : U.card ≤ k := hind U hUind
    have hRcard : R.card = 2*k := by
      have hh := Finset.card_compl C
      simp only [Fintype.card_fin] at hh
      dsimp [R]
      omega
    have hRset : (R : Set (Fin (4*k))) = (C : Set (Fin (4*k)))ᶜ := by ext x; simp [R]
    have hNR : N.verts ⊆ (R : Set (Fin (4*k))) := by simpa [hRset] using hNC
    apply balanced_cut_near_perfect_of_incidence_bounds k G hdegree C hcard M hM hMC
    · simpa [U,D] using hindU
    · intro r hr hm
      have hDcard : D.card = 2*M.edgeSet.ncard := by
        dsimp [D]
        rw [← Set.ncard_eq_toFinset_card']
        exact (in1076_matching_twice_card hM).symm
      have hUcard : U.card = 2*r := by
        have hh := Finset.card_sdiff_add_card_eq_card hDC
        dsimp [U]
        omega
      have hstar := maximum_matching_uncovered_incidence_independence_bound G C U M hM hMC hmaxM
        (by rfl) (2*r) k (by omega) hUcard hcard hind
      have hforbid : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∀ x ∈ R, ∀ y ∈ R,
          G.Adj u x → G.Adj v y → ¬ G.Adj x y := by
        intro u hu v hv huv x hx y hy hux hvy hxy
        have hxC : x ∉ C := by simpa [R] using hx
        have hyC : y ∉ C := by simpa [R] using hy
        exact two_crossing_adjacent_endpoints_impossible k G hext (by intro z; have hh := hdegree z; omega)
          C hcard M N hM hN hMC hNC hmaxM hmaxN heq (by omega)
          u v x y (hUC hu) (hUC hv) huv (hUn u hu) (hUn v hv) hxC hyC hux hvy hxy
      have hcross := no_two_crossing_matching_independence_incidence_bound G U R r k (by omega)
        hUcard hRcard N hN hNR (by omega) hforbid hind
      constructor
      · simpa [U,D] using hstar
      · simpa [U,D,R] using hcross
