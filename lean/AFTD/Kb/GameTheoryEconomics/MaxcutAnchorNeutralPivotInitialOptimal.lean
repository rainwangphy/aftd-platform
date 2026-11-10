import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorNeutralPivotGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityEqSum
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare

/-!
# maxcut_anchor_neutral_pivot_initial_optimal

Topic: equilibria   Node: d6ab15247465

Provenance: helper lemma. The existing optimal initial profile cuts the added edge.

The initial profile remains globally optimal after the extra edge is added.
-/

instance : DecidableRel maxcut_anchor_neutral_pivot_graph.Adj := by
  unfold maxcut_anchor_neutral_pivot_graph maxcut_anchor_three_graph
  infer_instance

lemma maxcut_anchor_neutral_pivot_initial_optimal_welfare_add_two
    {V : Type} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {k : ℕ} (σ : V → Fin k) (x y : V)
    (hH : ∀ u v, H.Adj u v → G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x)) :
    maxcut_welfare H σ ≤ maxcut_welfare G σ + 2 := by
  rw [maxcut_welfare, maxcut_welfare]
  have hterm : ∀ v : V, maxcut_utility H σ v ≤
      maxcut_utility G σ v + (if v = x then 1 else 0) + (if v = y then 1 else 0) := by
    intro v
    rw [maxcut_utility_eq_sum, maxcut_utility_eq_sum]
    have h1 : (∑ w, (if v = x ∧ w = y then 1 else 0 : ℕ)) = (if v = x then 1 else 0) := by
      by_cases hv : v = x
      · simp only [hv, if_true, true_and, Finset.sum_ite_eq']
        simp
      · simp [hv]
    have h2 : (∑ w, (if v = y ∧ w = x then 1 else 0 : ℕ)) = (if v = y then 1 else 0) := by
      by_cases hv : v = y
      · simp only [hv, if_true, true_and, Finset.sum_ite_eq']
        simp
      · simp [hv]
    calc ∑ w, (if H.Adj v w ∧ σ w ≠ σ v then 1 else 0)
        ≤ ∑ w, ((if G.Adj v w ∧ σ w ≠ σ v then 1 else 0) + (if v = x ∧ w = y then 1 else 0) + (if v = y ∧ w = x then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro w _
          by_cases h : H.Adj v w ∧ σ w ≠ σ v
          · rw [if_pos h]
            rcases hH v w h.1 with hg | ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
            · rw [if_pos ⟨hg, h.2⟩]; omega
            · rw [if_pos (show v = x ∧ w = y from ⟨hr1, hr2⟩)]; omega
            · rw [if_pos (show v = y ∧ w = x from ⟨hr1, hr2⟩)]; omega
          · rw [if_neg h]; exact Nat.zero_le _
      _ = (∑ w, (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0)) + (if v = x then 1 else 0) + (if v = y then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2]
  calc ∑ v, maxcut_utility H σ v
      ≤ ∑ v, (maxcut_utility G σ v + (if v = x then 1 else 0) + (if v = y then 1 else 0)) :=
        Finset.sum_le_sum fun v _ => hterm v
    _ = ∑ v, maxcut_utility G σ v + 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hx : (∑ v : V, if v = x then (1:ℕ) else 0) = 1 := by
          rw [Finset.sum_ite_eq']; simp
        have hy : (∑ v : V, if v = y then (1:ℕ) else 0) = 1 := by
          rw [Finset.sum_ite_eq']; simp
        rw [hx, hy]

lemma maxcut_anchor_neutral_pivot_initial_optimal_welfare_add_two_le
    {V : Type} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {k : ℕ} (σ : V → Fin k) (x y : V)
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (hnew : ¬ G.Adj x y) (hcolor : σ x ≠ σ y) :
    maxcut_welfare G σ + 2 ≤ maxcut_welfare H σ := by
  have hxy : x ≠ y := fun h => hcolor (by rw [h])
  rw [maxcut_welfare, maxcut_welfare]
  have hterm : ∀ v : V, maxcut_utility G σ v + (if v = x then 1 else 0) + (if v = y then 1 else 0) ≤ maxcut_utility H σ v := by
    intro v
    rw [maxcut_utility, maxcut_utility]
    by_cases hvx : v = x
    · subst v
      have hsub : insert y (Finset.univ.filter fun w => G.Adj x w ∧ σ w ≠ σ x) ⊆
          (Finset.univ.filter fun w => H.Adj x w ∧ σ w ≠ σ x) := by
        rw [Finset.insert_subset_iff]
        refine ⟨?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(hH x y).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), hcolor.symm⟩
        · intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          exact ⟨(hH x w).mpr (Or.inl hw.1), hw.2⟩
      have hnot : y ∉ (Finset.univ.filter fun w => G.Adj x w ∧ σ w ≠ σ x) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h => hnew h.1
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at hcard
      rw [if_pos rfl, if_neg hxy]
      simpa using hcard
    · by_cases hvy : v = y
      · subst v
        have hsub : insert x (Finset.univ.filter fun w => G.Adj y w ∧ σ w ≠ σ y) ⊆
            (Finset.univ.filter fun w => H.Adj y w ∧ σ w ≠ σ y) := by
          rw [Finset.insert_subset_iff]
          refine ⟨?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨(hH y x).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)), hcolor⟩
          · intro w hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
            exact ⟨(hH y w).mpr (Or.inl hw.1), hw.2⟩
        have hnot : x ∉ (Finset.univ.filter fun w => G.Adj y w ∧ σ w ≠ σ y) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun h => hnew h.1.symm
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hnot] at hcard
        rw [if_neg hvx, if_pos rfl]
        simpa using hcard
      · have hsub : (Finset.univ.filter fun w => G.Adj v w ∧ σ w ≠ σ v) ⊆
            (Finset.univ.filter fun w => H.Adj v w ∧ σ w ≠ σ v) := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          exact ⟨(hH v w).mpr (Or.inl hw.1), hw.2⟩
        have hcard := Finset.card_le_card hsub
        rw [if_neg hvx, if_neg hvy]
        simpa using hcard
  have hsum : ∑ v, (maxcut_utility G σ v + (if v = x then 1 else 0) + (if v = y then 1 else 0))
      = ∑ v, maxcut_utility G σ v + 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hx : (∑ v : V, if v = x then (1:ℕ) else 0) = 1 := by
      rw [Finset.sum_ite_eq']; simp
    have hy : (∑ v : V, if v = y then (1:ℕ) else 0) = 1 := by
      rw [Finset.sum_ite_eq']; simp
    rw [hx, hy]
  calc ∑ v, maxcut_utility G σ v + 2
      = ∑ v, (maxcut_utility G σ v + (if v = x then 1 else 0) + (if v = y then 1 else 0)) := hsum.symm
    _ ≤ ∑ v, maxcut_utility H σ v := Finset.sum_le_sum fun v _ => hterm v

theorem maxcut_anchor_neutral_pivot_initial_optimal : is_maxcut_optimal maxcut_anchor_neutral_pivot_graph maxcut_anchor_three_initial_coloring := by
  intro τ
  letI : DecidableRel maxcut_anchor_three_graph.Adj := by unfold maxcut_anchor_three_graph; infer_instance
  have hAdj : ∀ u v : Fin 16 ⊕ (Fin 3 × Fin 25),
      maxcut_anchor_neutral_pivot_graph.Adj u v ↔
        maxcut_anchor_three_graph.Adj u v ∨
          (u = Sum.inl 0 ∧ v = Sum.inr ((2:Fin 3), (24:Fin 25))) ∨
          (u = Sum.inr ((2:Fin 3), (24:Fin 25)) ∧ v = Sum.inl 0) := by
    intro u v
    unfold maxcut_anchor_neutral_pivot_graph
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, (h | ⟨e1, e2⟩) | (h | ⟨e1, e2⟩)⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨e1, e2⟩)
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨e2, e1⟩)
    · rintro (h | ⟨e1, e2⟩ | ⟨e1, e2⟩)
      · exact ⟨maxcut_anchor_three_graph.ne_of_adj h, Or.inl (Or.inl h)⟩
      · subst u; subst v
        refine ⟨?_, ?_⟩
        · simp
        · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      · subst u; subst v
        refine ⟨?_, ?_⟩
        · simp
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hnew : ¬ maxcut_anchor_three_graph.Adj (Sum.inl 0) (Sum.inr ((2:Fin 3), (24:Fin 25))) := by
    decide
  have hcolor : maxcut_anchor_three_initial_coloring (Sum.inl 0) ≠
      maxcut_anchor_three_initial_coloring (Sum.inr ((2:Fin 3), (24:Fin 25))) := by
    decide
  have hupper : maxcut_welfare maxcut_anchor_neutral_pivot_graph τ ≤
      maxcut_welfare maxcut_anchor_three_graph τ + 2 :=
    maxcut_anchor_neutral_pivot_initial_optimal_welfare_add_two τ
      (Sum.inl 0) (Sum.inr ((2:Fin 3), (24:Fin 25)))
      (fun u v h => (hAdj u v).1 h)
  have hlower : maxcut_welfare maxcut_anchor_three_graph maxcut_anchor_three_initial_coloring + 2 ≤
      maxcut_welfare maxcut_anchor_neutral_pivot_graph maxcut_anchor_three_initial_coloring :=
    maxcut_anchor_neutral_pivot_initial_optimal_welfare_add_two_le
      maxcut_anchor_three_initial_coloring (Sum.inl 0) (Sum.inr ((2:Fin 3), (24:Fin 25)))
      hAdj hnew hcolor
  have hopt := maxcut_anchor_three_initial_optimal τ
  calc maxcut_welfare maxcut_anchor_neutral_pivot_graph τ
      ≤ maxcut_welfare maxcut_anchor_three_graph τ + 2 := hupper
    _ ≤ maxcut_welfare maxcut_anchor_three_graph maxcut_anchor_three_initial_coloring + 2 := by omega
    _ ≤ maxcut_welfare maxcut_anchor_neutral_pivot_graph maxcut_anchor_three_initial_coloring := hlower
