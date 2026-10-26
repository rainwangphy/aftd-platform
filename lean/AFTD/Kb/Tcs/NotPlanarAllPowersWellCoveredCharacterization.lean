import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsPlanar
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphCliqueBlowup
import AFTD.Kb.Tcs.ForallPowerWellCoveredOfWellCoveredDiamLeTwo
import AFTD.Kb.Tcs.SimpleGraphIsMinor
import AFTD.Kb.Tcs.G

/-!
# not_planar_all_powers_well_covered_characterization

Topic: graphs   Node: 6af065bb7f8a

Provenance: formalization of a published result. Source: arXiv:2610.09300 after Theorem 1.4 -- On graphs whose powers are well-covered

It is not the case that every finite connected simple planar graph G with at least two vertices whose powers G^d are all well-covered is either a complete graph of order at most 4 or a clique blow-up of the 5-cycle C_5.
-/

lemma not_planar_all_powers_well_covered_characterization_not_minor_of_card_lt {U V : Type*} [Fintype U] [Fintype V]
    (H : SimpleGraph U) (G : SimpleGraph V) (h : Fintype.card V < Fintype.card U) :
    ¬ simple_graph_is_minor H G := by
  classical
  intro ⟨B, hconn, hdisj, _⟩
  have hnonempty : ∀ u, ∃ x, x ∈ B u := fun u => (hconn u).nonempty.elim (fun ⟨x, hx⟩ => ⟨x, hx⟩)
  choose f hf using hnonempty
  have hinj : Function.Injective f := by
    intro u v huv
    by_contra hne
    have hd := hdisj u v hne
    exact Set.disjoint_iff.mp hd ⟨hf u, huv ▸ hf v⟩
  exact absurd h (not_lt_of_ge (Fintype.card_le_of_injective f hinj))

lemma not_planar_all_powers_well_covered_characterization_planar_of_card_le_four {V : Type*} [Fintype V] (G : SimpleGraph V) (h : Fintype.card V ≤ 4) :
    simple_graph_is_planar G := by
  unfold simple_graph_is_planar
  refine ⟨not_planar_all_powers_well_covered_characterization_not_minor_of_card_lt _ _ ?_,
          not_planar_all_powers_well_covered_characterization_not_minor_of_card_lt _ _ ?_⟩
  · simp; omega
  · simp; omega

theorem not_planar_all_powers_well_covered_characterization_c4_dist_le_two_aux :
    ∀ u v : Fin 4, u = v ∨ (SimpleGraph.cycleGraph 4).Adj u v ∨
      ∃ w : Fin 4, (SimpleGraph.cycleGraph 4).Adj u w ∧ (SimpleGraph.cycleGraph 4).Adj w v := by
  decide

theorem not_planar_all_powers_well_covered_characterization_c4_edist_le_two (u v : Fin 4) :
    (SimpleGraph.cycleGraph 4).edist u v ≤ 2 := by
  rcases not_planar_all_powers_well_covered_characterization_c4_dist_le_two_aux u v with rfl | h | ⟨w, h1, h2⟩
  · rw [SimpleGraph.edist_self]; norm_num
  · exact (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil).edist_le.trans (by simp)
  · exact (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)).edist_le.trans (by simp)

theorem not_planar_all_powers_well_covered_characterization_c4_diam_le_two :
    (SimpleGraph.cycleGraph 4).diam ≤ 2 := by
  have hediam : (SimpleGraph.cycleGraph 4).ediam ≤ 2 := by
    rw [SimpleGraph.ediam_le_iff]
    exact not_planar_all_powers_well_covered_characterization_c4_edist_le_two
  rw [SimpleGraph.diam]
  exact ENat.toNat_le_of_le_natCast hediam

theorem not_planar_all_powers_well_covered_characterization_c4_indep_card_le_two (s : Finset (Fin 4))
    (hs : (SimpleGraph.cycleGraph 4).IsIndepSet (s : Set (Fin 4))) :
    s.card ≤ 2 := by
  revert s hs
  decide

theorem not_planar_all_powers_well_covered_characterization_c4_indep_extend (s : Finset (Fin 4))
    (hs : (SimpleGraph.cycleGraph 4).IsIndepSet (s : Set (Fin 4))) (hcard : s.card < 2) :
    ∃ v : Fin 4, v ∉ s ∧ (SimpleGraph.cycleGraph 4).IsIndepSet ((insert v s : Finset (Fin 4)) : Set (Fin 4)) := by
  revert s hs hcard
  decide

theorem not_planar_all_powers_well_covered_characterization_c4_maximal_card (s : Finset (Fin 4))
    (hs : Maximal (fun u : Finset (Fin 4) => (SimpleGraph.cycleGraph 4).IsIndepSet (u : Set (Fin 4))) s) :
    s.card = 2 := by
  have hle : s.card ≤ 2 := not_planar_all_powers_well_covered_characterization_c4_indep_card_le_two s hs.1
  have hge : 2 ≤ s.card := by
    by_contra! hlt
    obtain ⟨v, hv_notin, hv_indep⟩ := not_planar_all_powers_well_covered_characterization_c4_indep_extend s hs.1 hlt
    have hsub : s ≤ insert v s := Finset.subset_insert v s
    have heq : insert v s ≤ s := hs.2 hv_indep hsub
    exact hv_notin (heq (Finset.mem_insert_self v s))
  omega

theorem not_planar_all_powers_well_covered_characterization_c4_is_well_covered :
    simple_graph_is_well_covered (SimpleGraph.cycleGraph 4) := by
  intro s t hs ht
  rw [not_planar_all_powers_well_covered_characterization_c4_maximal_card s hs,
      not_planar_all_powers_well_covered_characterization_c4_maximal_card t ht]

theorem not_planar_all_powers_well_covered_characterization_c4_all_powers_well_covered :
    ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power (SimpleGraph.cycleGraph 4) d) := by
  have hconn : (SimpleGraph.cycleGraph 4).Connected := @SimpleGraph.cycleGraph_connected 3
  exact forall_power_well_covered_of_well_covered_diam_le_two
    (SimpleGraph.cycleGraph 4) hconn
    not_planar_all_powers_well_covered_characterization_c4_diam_le_two
    not_planar_all_powers_well_covered_characterization_c4_is_well_covered

lemma not_planar_all_powers_well_covered_characterization_not_iso_top_c4 :
    ¬ ∃ k : ℕ, k ≤ 4 ∧ Nonempty (SimpleGraph.cycleGraph 4 ≃g (⊤ : SimpleGraph (Fin k))) := by
  intro ⟨k, hk, ⟨e⟩⟩
  have hcard : Fintype.card (Fin 4) = Fintype.card (Fin k) := Fintype.card_congr e.toEquiv
  simp only [Fintype.card_fin] at hcard
  subst hcard
  have hadj : (⊤ : SimpleGraph (Fin 4)).Adj (e 0) (e 2) := by
    rw [SimpleGraph.top_adj]
    intro h
    have : (0 : Fin 4) = 2 := e.injective h
    revert this; decide
  have h_c4 : (SimpleGraph.cycleGraph 4).Adj 0 2 := e.map_adj_iff.mp hadj
  revert h_c4
  decide

lemma not_planar_all_powers_well_covered_characterization_not_iso_blowup_c4 :
    ¬ ∃ a : Fin 5 → ℕ, (∀ i, 0 < a i) ∧ Nonempty (simple_graph_clique_blowup (SimpleGraph.cycleGraph 5) a ≃g SimpleGraph.cycleGraph 4) := by
  intro ⟨a, ha, ⟨e⟩⟩
  have hcard : Fintype.card (Σ i : Fin 5, Fin (a i)) = Fintype.card (Fin 4) := Fintype.card_congr e.toEquiv
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin] at hcard
  have hsum : 5 ≤ ∑ i : Fin 5, a i := by
    have : ∑ i : Fin 5, (1 : ℕ) ≤ ∑ i : Fin 5, a i := Finset.sum_le_sum (fun i _ => ha i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    exact this
  omega

/-- Refutation of the OP-161 characterization: not every finite connected planar graph with all powers well-covered is a complete graph of order at most 4 or a clique blow-up of C_5 (C_7 is a counterexample). -/
theorem not_planar_all_powers_well_covered_characterization :
    ¬ (∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected →
      simple_graph_is_planar G →
      2 ≤ Fintype.card V →
      (∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d)) →
      (∃ k : ℕ, k ≤ 4 ∧ Nonempty (G ≃g (⊤ : SimpleGraph (Fin k)))) ∨
      (∃ a : Fin 5 → ℕ, (∀ i, 0 < a i) ∧ Nonempty (simple_graph_clique_blowup (SimpleGraph.cycleGraph 5) a ≃g G))) := by
  intro h
  have hconn : (SimpleGraph.cycleGraph 4).Connected := @SimpleGraph.cycleGraph_connected 3
  have hplanar : simple_graph_is_planar (SimpleGraph.cycleGraph 4) :=
    not_planar_all_powers_well_covered_characterization_planar_of_card_le_four _ (by decide)
  have hcard : 2 ≤ Fintype.card (Fin 4) := by decide
  have hwc := not_planar_all_powers_well_covered_characterization_c4_all_powers_well_covered
  rcases h (SimpleGraph.cycleGraph 4) hconn hplanar hcard hwc with h1 | h2
  · exact not_planar_all_powers_well_covered_characterization_not_iso_top_c4 h1
  · exact not_planar_all_powers_well_covered_characterization_not_iso_blowup_c4 h2
