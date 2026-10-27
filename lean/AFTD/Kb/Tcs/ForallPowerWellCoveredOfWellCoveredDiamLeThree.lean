import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphPowerOne

/-!
# forall_power_well_covered_of_well_covered_diam_le_three

Topic: graphs   Node: 6c8813606689

Provenance: helper lemma. arXiv:2610.09300; OP-537

Let G be a finite connected simple graph of diameter at most 3. If G and its second power G^2 are both well-covered, then every positive integer power G^d (for d ≥ 1) is well-covered.
-/

private lemma forall_power_well_covered_of_well_covered_diam_le_three_aux_indep_top_iff
    {V : Type*} (s : Finset V) :
    (⊤ : SimpleGraph V).IsIndepSet (↑s) ↔ s.card ≤ 1 := by
  constructor
  · intro h
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    exact (h ha hb hab) hab
  · intro h
    rw [Finset.card_le_one] at h
    intro a ha b hb hab
    exact fun hne => hne (h a ha b hb)

private lemma forall_power_well_covered_of_well_covered_diam_le_three_aux_top_card_eq_one
    {V : Type*} [Nonempty V] (s : Finset V)
    (hs : Maximal (fun u : Finset V => (⊤ : SimpleGraph V).IsIndepSet (↑u)) s) :
    s.card = 1 := by
  have hle : s.card ≤ 1 :=
    forall_power_well_covered_of_well_covered_diam_le_three_aux_indep_top_iff s |>.mp hs.1
  have hpos : 0 < s.card := by
    rw [Finset.card_pos]
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨v⟩ := ‹Nonempty V›
    have ht : (⊤ : SimpleGraph V).IsIndepSet (↑({v} : Finset V)) := by
      rw [forall_power_well_covered_of_well_covered_diam_le_three_aux_indep_top_iff]; simp
    have hsub : s ≤ ({v} : Finset V) := by rw [hne]; exact Finset.empty_subset _
    have hle2 : ({v} : Finset V) ≤ s := hs.2 ht hsub
    have hv : v ∈ s := hle2 (by simp)
    rw [hne] at hv
    simp at hv
  omega

private lemma forall_power_well_covered_of_well_covered_diam_le_three_aux_top
    {V : Type*} [Fintype V] [Nonempty V] :
    simple_graph_is_well_covered (⊤ : SimpleGraph V) := by
  intro s t hs ht
  rw [forall_power_well_covered_of_well_covered_diam_le_three_aux_top_card_eq_one s hs,
    forall_power_well_covered_of_well_covered_diam_le_three_aux_top_card_eq_one t ht]

/-- A connected graph of diameter at most 3 has all powers well-covered if G and G^2 are well-covered. -/
theorem forall_power_well_covered_of_well_covered_diam_le_three {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (hdiam : G.diam ≤ 3)
    (hwc1 : simple_graph_is_well_covered G)
    (hwc2 : simple_graph_is_well_covered (simple_graph_power G 2)) :
    ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d) := by
  haveI : Nonempty V := hconn.nonempty
  have hne_ediam : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp hconn
  have htop : ∀ d : ℕ, 3 ≤ d → simple_graph_power G d = ⊤ := by
    intro d hd
    ext u v
    constructor
    · intro h; exact h.1
    · intro huv
      refine ⟨huv, ?_⟩
      have hreach : G.Reachable u v := hconn u v
      have hne : G.edist u v ≠ ⊤ := SimpleGraph.edist_ne_top_iff_reachable.mpr hreach
      have htoNat : (G.edist u v).toNat ≤ G.diam :=
        ENat.toNat_le_toNat SimpleGraph.edist_le_ediam hne_ediam
      have heq : G.edist u v = ((G.edist u v).toNat : ℕ∞) :=
        (ENat.natCast_toNat_eq_self.mpr hne).symm
      rw [heq]
      have hle : (G.edist u v).toNat ≤ d := le_trans htoNat (le_trans hdiam hd)
      exact_mod_cast hle
  intro d hd
  rcases d with _ | _ | _ | k
  · omega
  · rw [simple_graph_power_one]; exact hwc1
  · exact hwc2
  · have htopd : simple_graph_power G (k + 3) = ⊤ := htop (k + 3) (by omega)
    rw [htopd]
    exact forall_power_well_covered_of_well_covered_diam_le_three_aux_top
