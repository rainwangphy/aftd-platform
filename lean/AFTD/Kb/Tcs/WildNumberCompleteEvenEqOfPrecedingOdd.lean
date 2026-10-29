import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraphLargeEq
import AFTD.Kb.Tcs.WildNumberCompleteOddEqIffOptimalPartition
import AFTD.Kb.Tcs.CompleteGraphOddLineGraphChromaticNumberEq
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_number_complete_even_eq_of_preceding_odd

Topic: graphs   Node: e703ec26be89

Provenance: helper lemma. General parity reduction for the OP-306 campaign, related to arXiv:2610.22142 Section3.3.3 and the existing deleted-vertex partition-lifting proof. This is a conditional transfer and equivalence, not an assertion that the unresolved odd-order cases hold.

For odd n>=3, if every proper n-coloring of K_n has the conjectured sharp wild number, then every minimum proper coloring of K_(n+1) has the conjectured sharp wild number.
-/

open scoped Classical
set_option maxHeartbeats 1000000

theorem wild_number_complete_even_eq_of_preceding_odd (n k : ℕ) (hn : 3 ≤ n) (hodd : n%2=1)
    (hsharp : ∀ cc : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n),
      simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) cc = 4*((n+1)/2)/3)
    (hk : (⊤ : SimpleGraph (Fin (n+1))).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin (n+1))).lineGraph.Coloring (Fin k)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin (n+1))) c = 4*((n+2)/2)/3 := by
  have hkn := wsc_even_min_colors hn hodd hk c
  subst k
  let cc := wsc_restrict_color c
  have hkodd := complete_graph_odd_line_graph_chromatic_number_eq n hn hodd
  obtain ⟨p,r,hr,hmin,hcut⟩ := (wild_number_complete_odd_eq_iff_optimal_partition hn hodd hkodd cc).1 (hsharp cc)
  obtain ⟨m,hm⟩ := wsc_missing_vertex_equiv_of_le n n hn hodd le_rfl cc
  have hcuts : ∀ (i : Fin n) (S : Finset (Fin (n/3))), S.Nonempty → S ≠ Finset.univ →
      ∃ (u v : Fin n) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ cc ⟨s(u,v),wild_kn_mem huv⟩ = i := by
    intro i S hS hproper
    obtain ⟨e,he⟩ := wsc_color_used hn cc m hm i
    obtain ⟨u,v,huv,hu,hv,hc⟩ := hcut e S hS hproper
    exact ⟨u,v,huv,hu,hv,hc.trans he⟩
  have hu := wsc_even_upper_of_partition (by omega) c p r hr hcuts
  have he : n-n/3 = 4*((n+2)/2)/3 := by omega
  rw [he] at hu
  exact le_antisymm hu (wild_number_complete_graph_min_proper_coloring_ge (n+1) n (by omega) hk c)
