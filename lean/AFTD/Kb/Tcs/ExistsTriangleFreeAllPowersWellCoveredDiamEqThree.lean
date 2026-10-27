import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.ForallPowerWellCoveredOfWellCoveredDiamLeThree
import AFTD.Kb.Tcs.CycleSevenDiamEqThree
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered

/-!
# exists_triangle_free_all_powers_well_covered_diam_eq_three

Topic: graphs   Node: ba2274c18874

Provenance: original. Related work: arXiv:2610.09300, Example 3.8

There exists a finite connected triangle-free simple graph G with at least two vertices whose diameter is exactly 3 and such that every positive integer power G^d (for d ≥ 1) is well-covered.
-/

def exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq : SimpleGraph (Fin 7) where
  Adj u v := u ≠ v ∧ ((SimpleGraph.cycleGraph 7).Adj u v ∨ ((SimpleGraph.cycleGraph 7).neighborFinset u ∩ (SimpleGraph.cycleGraph 7).neighborFinset v).Nonempty)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h1 | h2
    · left; exact h1.symm
    · right; rw [Finset.inter_comm]; exact h2⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (u v : Fin 7) : Decidable (exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq.Adj u v) := by
  dsimp [exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq]
  infer_instance

lemma exists_triangle_free_all_powers_well_covered_diam_eq_three_neighborFinset_inter_nonempty (u v : Fin 7) :
    ((SimpleGraph.cycleGraph 7).neighborFinset u ∩ (SimpleGraph.cycleGraph 7).neighborFinset v).Nonempty ↔
      ((SimpleGraph.cycleGraph 7).commonNeighbors u v).Nonempty := by
  simp [Finset.Nonempty, Set.Nonempty, SimpleGraph.mem_commonNeighbors]

lemma exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq_eq :
    simple_graph_power (SimpleGraph.cycleGraph 7) 2 = exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq := by
  ext u v
  dsimp [simple_graph_power, exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq]
  rw [exists_triangle_free_all_powers_well_covered_diam_eq_three_neighborFinset_inter_nonempty]
  rw [← not_lt, SimpleGraph.two_lt_edist_iff, Set.nonempty_iff_ne_empty]
  tauto

lemma exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq_wc :
    simple_graph_is_well_covered (simple_graph_power (SimpleGraph.cycleGraph 7) 2) := by
  rw [exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq_eq]
  have test1 : ∀ (s : Finset (Fin 7)), exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq.IsIndepSet ↑s → s.card ≤ 2 := by decide
  have test2 : ∀ (s : Finset (Fin 7)), exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq.IsIndepSet ↑s → s.card < 2 →
      ∃ v ∉ s, exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq.IsIndepSet ↑(insert v s) := by decide
  intro s t hs ht
  have hcard : ∀ u : Finset (Fin 7), Maximal (fun w : Finset (Fin 7) => exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq.IsIndepSet (w : Set (Fin 7))) u → u.card = 2 := by
    intro u hu
    apply le_antisymm (test1 u hu.1)
    by_contra hlt
    have hlt' : u.card < 2 := lt_of_not_ge hlt
    obtain ⟨v, hv, hind⟩ := test2 u hu.1 hlt'
    have hsub : u ≤ insert v u := Finset.subset_insert v u
    have heq := hu.2 hind hsub
    have : v ∈ u := heq (Finset.mem_insert_self v u)
    exact hv this
  rw [hcard s hs, hcard t ht]

lemma exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_wc :
    simple_graph_is_well_covered (SimpleGraph.cycleGraph 7) := by
  have test1 : ∀ (s : Finset (Fin 7)), (SimpleGraph.cycleGraph 7).IsIndepSet ↑s → s.card ≤ 3 := by decide
  have test2 : ∀ (s : Finset (Fin 7)), (SimpleGraph.cycleGraph 7).IsIndepSet ↑s → s.card < 3 →
      ∃ v ∉ s, (SimpleGraph.cycleGraph 7).IsIndepSet ↑(insert v s) := by decide
  intro s t hs ht
  have hcard : ∀ u : Finset (Fin 7), Maximal (fun w : Finset (Fin 7) => (SimpleGraph.cycleGraph 7).IsIndepSet (w : Set (Fin 7))) u → u.card = 3 := by
    intro u hu
    apply le_antisymm (test1 u hu.1)
    by_contra hlt
    have hlt' : u.card < 3 := lt_of_not_ge hlt
    obtain ⟨v, hv, hind⟩ := test2 u hu.1 hlt'
    have hsub : u ≤ insert v u := Finset.subset_insert v u
    have heq := hu.2 hind hsub
    have : v ∈ u := heq (Finset.mem_insert_self v u)
    exact hv this
  rw [hcard s hs, hcard t ht]

/-- The diameter-3 bound for triangle-free graphs whose powers are all well-covered is sharp (witnessed by C_7). -/
theorem exists_triangle_free_all_powers_well_covered_diam_eq_three :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.Connected ∧
      G.CliqueFree 3 ∧
      2 ≤ Fintype.card V ∧
      G.diam = 3 ∧
      (∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d)) := by
  refine ⟨Fin 7, inferInstance, SimpleGraph.cycleGraph 7, ?_, ?_, ?_, ?_, ?_⟩
  · exact SimpleGraph.cycleGraph_connected (n := 6)
  · intro t ht
    have : ∀ s : Finset (Fin 7), s.card = 3 → ¬ (SimpleGraph.cycleGraph 7).IsClique ↑s := by decide
    exact this t ht.card_eq ht.isClique
  · decide
  · exact cycle_seven_diam_eq_three
  · exact forall_power_well_covered_of_well_covered_diam_le_three
      (SimpleGraph.cycleGraph 7)
      (SimpleGraph.cycleGraph_connected (n := 6))
      (le_of_eq cycle_seven_diam_eq_three)
      exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_wc
      exists_triangle_free_all_powers_well_covered_diam_eq_three_c7_sq_wc
