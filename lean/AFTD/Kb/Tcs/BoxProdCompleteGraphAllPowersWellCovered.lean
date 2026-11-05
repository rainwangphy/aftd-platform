import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphIsWellCoveredBot

/-!
# boxProd_completeGraph_all_powers_well_covered

Topic: graphs   Node: cc85c1b27d48

Provenance: formalization of a published result. Source: arXiv:2611.03956 Theorem 2.11 (1)

Let G be a finite connected nontrivial graph, and let t be an integer with t > |V(G)|. If every positive power G^d (d ≥ 1) is well-covered, then every positive power of the Cartesian product G □ K_t is well-covered.
-/

/-- If G has well-covered powers and t > |V(G)|, then G □ K_t has well-covered powers. -/
theorem boxProd_completeGraph_all_powers_well_covered
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hnontriv : 2 ≤ Fintype.card V)
    (hwc : ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d))
    (t : ℕ) (ht : Fintype.card V < t) :
    ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power (G □ SimpleGraph.completeGraph (Fin t)) d) := by
  classical
  have hpow0 : simple_graph_power G 0 = ⊥ := by
    ext u v
    simp only [simple_graph_power, SimpleGraph.bot_adj]
    constructor
    · intro h
      have hz : G.edist u v = 0 := le_antisymm (by simpa using h.2) bot_le
      exact h.1 (SimpleGraph.edist_eq_zero_iff.mp hz)
    · intro h; exact h.elim
  have hinj : ∀ (d : ℕ) (s : Finset (V × Fin t)), 1 ≤ d →
      (simple_graph_power (G □ SimpleGraph.completeGraph (Fin t)) d).IsIndepSet ((s : Set (V × Fin t))) →
      Set.InjOn Prod.fst ((s : Set (V × Fin t))) := by
    intro d s hd h
    rw [SimpleGraph.isIndepSet_iff] at h
    intro p hp q hq hpq
    by_contra hne
    have hpair := h hp hq hne
    apply hpair
    have hd2 : p.2 ≠ q.2 := by
      intro hc
      exact hne (Prod.ext hpq hc)
    refine ⟨hne, ?_⟩
    show (G □ SimpleGraph.completeGraph (Fin t)).edist p q ≤ (d : ℕ∞)
    rw [SimpleGraph.edist_boxProd]
    have h1 : G.edist p.1 q.1 = 0 := by rw [hpq]; exact SimpleGraph.edist_self
    rw [h1]
    have hk : (SimpleGraph.completeGraph (Fin t)).edist p.2 q.2 ≤ 1 := by
      rw [SimpleGraph.completeGraph_eq_top, SimpleGraph.edist_top]
      split <;> simp
    calc (0 : ℕ∞) + (SimpleGraph.completeGraph (Fin t)).edist p.2 q.2
        = (SimpleGraph.completeGraph (Fin t)).edist p.2 q.2 := zero_add _
      _ ≤ 1 := hk
      _ ≤ (d : ℕ∞) := by exact_mod_cast hd
  have hcard : ∀ (d : ℕ) (s : Finset (V × Fin t)), 1 ≤ d →
      (simple_graph_power (G □ SimpleGraph.completeGraph (Fin t)) d).IsIndepSet ((s : Set (V × Fin t))) →
      (s.image Prod.fst).card = s.card := by
    intro d s hd h
    exact Finset.card_image_of_injOn (hinj d s hd h)
  have hdom : ∀ (d : ℕ) (s : Finset (V × Fin t)), 1 ≤ d →
      Maximal (fun u : Finset (V × Fin t) => (simple_graph_power (G □ SimpleGraph.completeGraph (Fin t)) d).IsIndepSet (↑u)) s →
      ∀ v : V, v ∉ s.image Prod.fst →
      ∃ w ∈ s.image Prod.fst, G.edist v w ≤ ((d - 1 : ℕ) : ℕ∞) := by
    intro d s hd hs v hv
    by_contra hcon
    push_neg at hcon
    have hscard_eq : (s.image Prod.fst).card = s.card := hcard d s hd hs.1
    have hscard_le : s.card ≤ Fintype.card V := by
      rw [← hscard_eq]; exact Finset.card_le_univ _
    set bad : Finset (Fin t) := (s.filter (fun p => G.edist v p.1 = (d : ℕ∞))).image Prod.snd with hbad_def
    have hbad_card : bad.card ≤ s.card := by
      rw [hbad_def]
      exact le_trans Finset.card_image_le (Finset.card_filter_le _ _)
    have hbad_lt : bad.card < t := lt_of_le_of_lt (le_trans hbad_card hscard_le) ht
    have hex : ∃ i : Fin t, i ∉ bad := by
      by_contra hc
      push_neg at hc
      have huniv : bad = Finset.univ := Finset.eq_univ_iff_forall.2 hc
      rw [huniv] at hbad_lt
      simp at hbad_lt
    obtain ⟨i, hi⟩ := hex
    have hnonadj : ∀ b ∈ s, ¬ (simple_graph_power (G □ SimpleGraph.completeGraph (Fin t)) d).Adj (v, i) b := by
      intro b hb hadj
      obtain ⟨w, j⟩ := b
      have hw : w ∈ s.image Prod.fst := Finset.mem_image.2 ⟨(w, j), hb, rfl⟩
      have hlt : ((d - 1 : ℕ) : ℕ∞) < G.edist v w := hcon w hw
      have hdle : (d : ℕ∞) ≤ G.edist v w := by
        have hadd : ((d - 1 : ℕ) : ℕ∞) + 1 ≤ G.edist v w := Order.add_one_le_of_lt hlt
        have harith : ((d - 1 : ℕ) : ℕ∞) + 1 = (d : ℕ∞) := by
          have hh : (d - 1 : ℕ) + 1 = d := Nat.sub_add_cancel hd
          rw [← hh]; push_cast; ring
        rwa [harith] at hadd
      have hHlt : (d : ℕ∞) < (G □ SimpleGraph.completeGraph (Fin t)).edist (v, i) (w, j) := by
        rw [SimpleGraph.edist_boxProd]
        by_cases heq : G.edist v w = (d : ℕ∞)
        · have hmem : (w, j) ∈ s.filter (fun p => G.edist v p.1 = (d : ℕ∞)) :=
            Finset.mem_filter.2 ⟨hb, heq⟩
          have hj : j ∈ bad := by
            rw [hbad_def]; exact Finset.mem_image.2 ⟨(w,j), hmem, rfl⟩
          have hij : i ≠ j := fun h => hi (h ▸ hj)
          have hK : (SimpleGraph.completeGraph (Fin t)).edist i j = 1 := by
            rw [SimpleGraph.completeGraph_eq_top, SimpleGraph.edist_top]; simp [hij]
          rw [heq, hK]
          have harith : (d:ℕ∞) + 1 = ((d+1 : ℕ) : ℕ∞) := by rw [← Nat.cast_one, ← Nat.cast_add]
          rw [harith]
          exact_mod_cast Nat.lt_succ_self d
        · have hgrad : (d : ℕ∞) < G.edist v w := lt_of_le_of_ne hdle (Ne.symm heq)
          exact lt_of_lt_of_le hgrad (le_add_right (le_refl _))
      exact absurd hadj.2 (not_le.mpr hHlt)
    have hIns : (simple_graph_power (G □ SimpleGraph.completeGraph (Fin t)) d).IsIndepSet
        ((insert (v, i) s : Finset (V × Fin t)) : Set (V × Fin t)) := by
      rw [Finset.coe_insert, SimpleGraph.isIndepSet_iff, Set.pairwise_insert]
      refine ⟨(SimpleGraph.isIndepSet_iff _).1 hs.1, ?_⟩
      intro b hb hne
      exact ⟨hnonadj b hb, fun hba => hnonadj b hb hba.symm⟩
    have hsub : s ≤ insert (v, i) s := Finset.subset_insert _ _
    have hle := hs.2 hIns hsub
    have hmem : (v, i) ∈ s := hle (Finset.mem_insert_self _ _)
    exact hv (Finset.mem_image.2 ⟨(v, i), hmem, rfl⟩)
  have hpm : ∀ (d : ℕ) (s : Finset (V × Fin t)), 1 ≤ d →
      Maximal (fun u : Finset (V × Fin t) => (simple_graph_power (G □ SimpleGraph.completeGraph (Fin t)) d).IsIndepSet (↑u)) s →
      Maximal (fun u : Finset V => (simple_graph_power G (d - 1)).IsIndepSet (↑u)) (s.image Prod.fst) := by
    intro d s hd hs
    have hindep : (simple_graph_power G (d - 1)).IsIndepSet ((s.image Prod.fst : Finset V) : Set V) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro v hv w hw hvw
      rw [Finset.coe_image] at hv hw
      obtain ⟨p, hp, rfl⟩ := hv
      obtain ⟨q, hq, hwq⟩ := hw
      rw [← hwq] at hvw ⊢
      intro hadj
      have hpq_ne : p ≠ q := by intro hpq; exact hvw (by rw [hpq])
      have hsind : (simple_graph_power (G □ SimpleGraph.completeGraph (Fin t)) d).IsIndepSet ((s : Set (V × Fin t))) := hs.1
      rw [SimpleGraph.isIndepSet_iff] at hsind
      have hnonadj : ¬ (simple_graph_power (G □ SimpleGraph.completeGraph (Fin t)) d).Adj p q := hsind hp hq hpq_ne
      have hlt : (d : ℕ∞) < (G □ SimpleGraph.completeGraph (Fin t)).edist p q := by
        by_contra hc; exact hnonadj ⟨hpq_ne, not_lt.mp hc⟩
      have hadj' : G.edist p.1 q.1 ≤ ((d - 1 : ℕ) : ℕ∞) := hadj.2
      have hk : (SimpleGraph.completeGraph (Fin t)).edist p.2 q.2 ≤ 1 := by
        rw [SimpleGraph.completeGraph_eq_top, SimpleGraph.edist_top]; split <;> simp
      have hbound : (G □ SimpleGraph.completeGraph (Fin t)).edist p q ≤ (d : ℕ∞) := by
        rw [SimpleGraph.edist_boxProd]
        calc G.edist p.1 q.1 + (SimpleGraph.completeGraph (Fin t)).edist p.2 q.2
            ≤ ((d - 1 : ℕ) : ℕ∞) + 1 := add_le_add hadj' hk
          _ = (d : ℕ∞) := by
              have h : (d - 1 : ℕ) + 1 = d := Nat.sub_add_cancel hd
              rw [← h]; push_cast; ring
      exact absurd hbound (not_le.mpr hlt)
    refine ⟨hindep, ?_⟩
    intro D' hD' hsub v hvD'
    by_contra hv
    obtain ⟨w, hw, hed⟩ := hdom d s hd hs v hv
    have hwD' : w ∈ D' := hsub hw
    have hvw : v ≠ w := fun h => hv (h ▸ hw)
    rw [SimpleGraph.isIndepSet_iff] at hD'
    exact (hD' hvD' hwD' hvw) ⟨hvw, hed⟩
  have hAllPow : ∀ e : ℕ, simple_graph_is_well_covered (simple_graph_power G e) := by
    intro e
    rcases Nat.eq_zero_or_pos e with he | he
    · rw [he, hpow0]
      exact simple_graph_is_well_covered_bot
    · exact hwc e he
  intro d hd s t hs ht
  have hps := hpm d s hd hs
  have hpt := hpm d t hd ht
  have hD := hAllPow (d - 1) (s.image Prod.fst) (t.image Prod.fst) hps hpt
  have hcs := hcard d s hd hs.1
  have hct := hcard d t hd ht.1
  omega
