import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPowerOne
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# forall_power_well_covered_of_well_covered_diam_le_two

Topic: graphs   Node: 3233c45efe6f

Provenance: formalization of a published result. Source: arXiv:2610.09300 (On graphs whose powers are well-covered), Sec. 3, remark before Question 3.9 ('every well-covered graph of diameter 2 automatically satisfies this condition'); stated for diameter at most 2.

Let G be a finite connected well-covered graph of diameter at most 2. Then G^d is well-covered for every d ≥ 1.
-/

theorem forall_power_well_covered_of_well_covered_diam_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (hdiam : G.diam ≤ 2)
    (hwc : simple_graph_is_well_covered G) :
    ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d) := by
  intro d hd
  rcases Nat.lt_or_ge d 2 with h1 | h2
  · have : d = 1 := by omega
    subst this
    rw [simple_graph_power_one]
    exact hwc
  · have : Nonempty V := hconn.nonempty
    have htop : G.ediam ≠ ⊤ := (SimpleGraph.connected_iff_ediam_ne_top).1 hconn
    have hed : ∀ u v : V, G.edist u v ≤ d := by
      intro u v
      calc G.edist u v ≤ G.ediam := SimpleGraph.edist_le_ediam
        _ = G.diam := by rw [SimpleGraph.diam]; exact (ENat.natCast_toNat htop).symm
        _ ≤ d := by exact_mod_cast hdiam.trans h2
    have hcard : ∀ s : Finset V,
        Maximal (fun u : Finset V => (simple_graph_power G d).IsIndepSet (u : Set V)) s →
          s.card = 1 := by
      intro s hs
      rw [Finset.card_eq_one]
      obtain ⟨v⟩ := ‹Nonempty V›
      by_cases hne : s.Nonempty
      · obtain ⟨a, ha⟩ := hne
        refine ⟨a, Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun b hb => ?_⟩⟩
        by_contra hba
        exact hs.1 hb ha hba ⟨hba, hed b a⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        subst hne
        have hv : (simple_graph_power G d).IsIndepSet (({v} : Finset V) : Set V) := by simp
        have := hs.2 hv (Finset.empty_subset _)
        simp at this
    intro s t hs ht
    rw [hcard s hs, hcard t ht]
