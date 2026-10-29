import AFTD.Prelude
import AFTD.Kb.Tcs.WildOddOptimalColorConnectingPartition
import AFTD.Kb.Tcs.SimpleGraphWildNumberAttained
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfBlockCutCondition
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.Tcs.SimpleGraphWildNumber

/-!
# wild_number_complete_odd_eq_iff_optimal_partition

Topic: graphs   Node: 8d8ad11cdfcc

Provenance: helper lemma. Structural necessity and certificate-soundness helpers for the OP-306 campaign; arXiv:2610.22142, Sections 3.3.1 and 3.3.2. These make the optimal block-partition route an equivalence at every odd order; no new exact wild-number case or bound is asserted.

For every minimum proper coloring of K_n at odd order n>=3, its wild number equals floor(4*ceil(n/2)/3) if and only if there is a rooted partition into floor(n/3) blocks of at least three vertices such that every used color crosses every nonempty proper block cut.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_number_complete_odd_eq_iff_optimal_partition {n k : ℕ} (hn : 3 ≤ n) (hodd : n%2=1)
    (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c = 4*((n+1)/2)/3 ↔
    ∃ (p : Fin n → Fin (n/3)) (r : Fin (n/3) → Fin n),
      (∀ t, p (r t) = t) ∧
      (∀ t, 3 ≤ ((Finset.univ : Finset (Fin n)).filter fun v => p v = t).card) ∧
      (∀ (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (S : Finset (Fin (n/3))),
        S.Nonempty → S ≠ Finset.univ →
        ∃ (u v : Fin n) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ c ⟨s(u,v),wild_kn_mem huv⟩ = c e) := by
  have he : 4*((n+1)/2)/3 = n-n/3 := by omega
  constructor
  · intro h
    letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
    obtain ⟨W,hcard,hW⟩ := simple_graph_wild_number_attained (⊤ : SimpleGraph (Fin n)) c SimpleGraph.connected_top
    apply wild_odd_optimal_color_connecting_partition hn hodd c W hW
    rw [hcard,h,he]
  · rintro ⟨p,r,hr,hmin,hcut⟩
    apply le_antisymm
    · rw [he]
      exact simple_graph_wild_number_le_of_block_cut_condition (by omega) c p r hr hcut
    · exact wild_number_complete_graph_min_proper_coloring_ge n k hn hk c
