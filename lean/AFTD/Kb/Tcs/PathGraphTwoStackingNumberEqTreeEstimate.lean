import AFTD.Prelude
import AFTD.Kb.Tcs.GraphStackingNumber
import AFTD.Kb.Tcs.SimpleGraphTreeEstimate
import AFTD.Kb.Tcs.GraphPebblingStep
import AFTD.Kb.Tcs.GraphConfigStackable

/-!
# path_graph_two_stacking_number_eq_tree_estimate

Topic: graphs   Node: 479168406d82

Provenance: original. Related work: arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Conjecture 5.6, smallest nontrivial tree; the paper's Theorem 4.4 (from earlier work) gives stack(P_n) = 2^n − 1.

Conjecture 5.6 (OP-144) holds for the path on two vertices: stack(P₂) = estim(P₂) (both equal 3).
-/

lemma path_graph_two_stacking_number_eq_tree_estimate_degree
    [DecidableRel (SimpleGraph.pathGraph 2).Adj] (v : Fin 2) :
    (SimpleGraph.pathGraph 2).degree v = 1 := by
  have : (SimpleGraph.pathGraph 2).neighborFinset v = Finset.univ.erase v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj, Finset.mem_erase,
      Finset.mem_univ, and_true]
    fin_cases v <;> fin_cases w <;> decide
  rw [SimpleGraph.degree, this]
  simp

lemma path_graph_two_stacking_number_eq_tree_estimate_tree_estimate
    [DecidableRel (SimpleGraph.pathGraph 2).Adj] :
    simple_graph_tree_estimate (SimpleGraph.pathGraph 2) = 3 := by
  unfold simple_graph_tree_estimate
  have h_deg : ∀ v : Fin 2, (SimpleGraph.pathGraph 2).degree v = 1 :=
    path_graph_two_stacking_number_eq_tree_estimate_degree
  have h_r : ∀ r : Fin 2,
    (∑ v ∈ Finset.univ.filter (fun v => v = r ∨ 1 < (SimpleGraph.pathGraph 2).degree v),
      (SimpleGraph.pathGraph 2).degree v * 2 ^ (SimpleGraph.pathGraph 2).dist r v) +
    (Finset.univ.filter (fun v => v ≠ r ∧ (SimpleGraph.pathGraph 2).degree v = 1)).card = 2 := by
    intro r
    have hfilt1 : Finset.univ.filter (fun v => v = r ∨ 1 < (SimpleGraph.pathGraph 2).degree v) = {r} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, h_deg]
      omega
    have hfilt2 : Finset.univ.filter (fun v => v ≠ r ∧ (SimpleGraph.pathGraph 2).degree v = 1) =
        Finset.univ.erase r := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true, h_deg]
    rw [hfilt1, hfilt2]
    simp [h_deg, SimpleGraph.dist_self]
  have h_sup : Finset.univ.sup (fun r : Fin 2 =>
    (∑ v ∈ Finset.univ.filter (fun v => v = r ∨ 1 < (SimpleGraph.pathGraph 2).degree v),
      (SimpleGraph.pathGraph 2).degree v * 2 ^ (SimpleGraph.pathGraph 2).dist r v) +
    (Finset.univ.filter (fun v => v ≠ r ∧ (SimpleGraph.pathGraph 2).degree v = 1)).card) = 2 := by
    apply le_antisymm
    · refine Finset.sup_le ?_
      intro r _
      rw [h_r r]
    · refine le_trans ?_ (Finset.le_sup (f := fun r => _) (Finset.mem_univ 0))
      rw [h_r 0]
  rw [h_sup]
  rfl

lemma path_graph_two_stacking_number_eq_tree_estimate_three_stackable
    (c : Fin 2 → ℕ) (hc : ∑ v, c v = 3) :
    graph_config_stackable (SimpleGraph.pathGraph 2) c := by
  rw [Fin.sum_univ_two] at hc
  have hcases : (c 0 = 3 ∧ c 1 = 0) ∨ (c 0 = 2 ∧ c 1 = 1) ∨
                (c 0 = 1 ∧ c 1 = 2) ∨ (c 0 = 0 ∧ c 1 = 3) := by omega
  rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine ⟨c, Relation.ReflTransGen.refl, 0, by omega, ?_⟩
    intro w hw; fin_cases w; contradiction; exact h1
  · let c' := Function.update (Function.update c 0 (c 0 - 2)) 1 (c 1 + 1)
    have hstep : graph_pebbling_step (SimpleGraph.pathGraph 2) c c' := by
      refine ⟨0, 1, ?_, ?_, rfl⟩
      · rw [SimpleGraph.pathGraph_adj]; decide
      · omega
    refine ⟨c', Relation.ReflTransGen.single hstep, 1, by dsimp [c']; simp, ?_⟩
    intro w hw; fin_cases w
    · dsimp [c']; simp [Function.update_of_ne, Function.update_self]; omega
    · contradiction
  · let c' := Function.update (Function.update c 1 (c 1 - 2)) 0 (c 0 + 1)
    have hstep : graph_pebbling_step (SimpleGraph.pathGraph 2) c c' := by
      refine ⟨1, 0, ?_, ?_, rfl⟩
      · rw [SimpleGraph.pathGraph_adj]; decide
      · omega
    refine ⟨c', Relation.ReflTransGen.single hstep, 0, by dsimp [c']; simp, ?_⟩
    intro w hw; fin_cases w
    · contradiction
    · dsimp [c']; simp [Function.update_of_ne, Function.update_self]; omega
  · refine ⟨c, Relation.ReflTransGen.refl, 1, by omega, ?_⟩
    intro w hw; fin_cases w; exact h0; contradiction

lemma path_graph_two_stacking_number_eq_tree_estimate_reflTransGen_eq_of_no_step
    {α : Type*} {R : α → α → Prop} {a b : α}
    (h : ∀ c, ¬ R a c) (hr : Relation.ReflTransGen R a b) : b = a := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ _ => exact (h _ hstep).elim

lemma path_graph_two_stacking_number_eq_tree_estimate_not_stackable_one_one :
    ¬ graph_config_stackable (SimpleGraph.pathGraph 2) (fun _ : Fin 2 => 1) := by
  intro ⟨c', hreach, v, _, hzero⟩
  have hno_step : ∀ d, ¬ graph_pebbling_step (SimpleGraph.pathGraph 2) (fun _ => 1) d := by
    intro d ⟨u, _, _, h2, _⟩
    dsimp at h2
    omega
  have hc' : c' = (fun _ => 1) :=
    path_graph_two_stacking_number_eq_tree_estimate_reflTransGen_eq_of_no_step hno_step hreach
  subst hc'
  fin_cases v
  · have := hzero 1 (by decide)
    contradiction
  · have := hzero 0 (by decide)
    contradiction

lemma path_graph_two_stacking_number_eq_tree_estimate_stacking_number :
    graph_stacking_number (SimpleGraph.pathGraph 2) = 3 := by
  unfold graph_stacking_number
  set S := {t : ℕ | 2 ≤ t ∧ ∀ c : Fin 2 → ℕ, ∑ v, c v = t →
    graph_config_stackable (SimpleGraph.pathGraph 2) c}
  have h3 : 3 ∈ S := by
    refine ⟨by decide, ?_⟩
    intro c hc
    exact path_graph_two_stacking_number_eq_tree_estimate_three_stackable c hc
  have hmin : ∀ t ∈ S, 3 ≤ t := by
    intro t ⟨ht2, ht_all⟩
    by_contra! hlt
    have ht : t = 2 := by omega
    have hsum : ∑ v : Fin 2, (fun _ : Fin 2 => 1 : Fin 2 → ℕ) v = 2 := by decide
    have hstack : graph_config_stackable (SimpleGraph.pathGraph 2) (fun _ => 1) := by
      subst ht
      exact ht_all (fun _ => 1) hsum
    exact path_graph_two_stacking_number_eq_tree_estimate_not_stackable_one_one hstack
  apply le_antisymm
  · exact Nat.sInf_le h3
  · exact le_csInf ⟨3, h3⟩ hmin

theorem path_graph_two_stacking_number_eq_tree_estimate
    [DecidableRel (SimpleGraph.pathGraph 2).Adj] :
    graph_stacking_number (SimpleGraph.pathGraph 2) =
      simple_graph_tree_estimate (SimpleGraph.pathGraph 2) := by
  rw [path_graph_two_stacking_number_eq_tree_estimate_stacking_number,
      path_graph_two_stacking_number_eq_tree_estimate_tree_estimate]
