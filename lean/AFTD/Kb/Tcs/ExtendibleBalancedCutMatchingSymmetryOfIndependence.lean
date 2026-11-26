import AFTD.Prelude
import AFTD.Kb.Tcs.MaximumMatchingSizeFromIndependence
import AFTD.Kb.Tcs.ExtendibleBalancedCutMaximumMatchingSizesEqual
import AFTD.Kb.Tcs.IsKExtendable

/-!
# extendible_balanced_cut_matching_symmetry_of_independence

Topic: graphs   Node: d1e685eebd3a

Provenance: helper lemma. Balanced-cut matching symmetry for OP-1957; https://arxiv.org/abs/2611.22690.

In the stated order-4k extendible graph with independence number at most k, maximum matchings in the balanced halves have equal size.
-/

theorem extendible_balanced_cut_matching_symmetry_of_independence
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) (hext : is_k_extendable G k)
    (hind : ∀ U : Finset (Fin (4*k)),
      (∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v) → U.card ≤ k)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching)
    (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hNC : N.verts ⊆ ((C : Set (Fin (4*k)))ᶜ))
    (hmaxM : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin (4*k))) → T.edgeSet.ncard ≤ M.edgeSet.ncard)
    (hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ ((C : Set (Fin (4*k)))ᶜ) → T.edgeSet.ncard ≤ N.edgeSet.ncard) :
    M.edgeSet.ncard = N.edgeSet.ncard := by
  set_option maxHeartbeats 4000000 in
    classical
    have hCcomp : ((Cᶜ : Finset (Fin (4*k))) : Set (Fin (4*k))) = (C : Set (Fin (4*k)))ᶜ := by ext v; simp
    have hCcompcard : (Cᶜ : Finset (Fin (4*k))).card = 2*k := by
      have h := Finset.card_compl C
      simp only [Fintype.card_fin] at h
      omega
    have hm := maximum_matching_size_from_independence G C M hM hMC hmaxM k hind
    have hn := maximum_matching_size_from_independence G (Cᶜ : Finset (Fin (4*k))) N hN
      (by simpa [hCcomp] using hNC) (by simpa [hCcomp] using hmaxN) k hind
    have hsum : k ≤ M.edgeSet.ncard+N.edgeSet.ncard := by omega
    exact extendible_balanced_cut_maximum_matching_sizes_equal k G hext C hcard M N hM hN hMC hNC hmaxM hmaxN hsum
