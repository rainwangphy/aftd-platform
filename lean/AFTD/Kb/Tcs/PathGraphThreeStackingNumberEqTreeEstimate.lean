import AFTD.Prelude
import AFTD.Kb.Tcs.GraphStackingNumber
import AFTD.Kb.Tcs.SimpleGraphTreeEstimate
import AFTD.Kb.Tcs.GraphPebblingStep
import AFTD.Kb.Tcs.GraphConfigStackable

/-!
# path_graph_three_stacking_number_eq_tree_estimate

Topic: graphs   Node: c23b4808d5fc

Provenance: original. Related work: arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Conjecture 5.6 for the path P₃; consistent with stack(P_n) = 2^n − 1 (Theorem 4.4, from earlier work).

Conjecture 5.6 (OP-144) holds for the path on three vertices: stack(P₃) = estim(P₃) (both equal 7).
-/

/-- Stacked triple on the three vertices of `P₃`. -/
def path_graph_three_stacked (a b c : ℕ) : Bool :=
  (0 < a && b = 0 && c = 0) || (a = 0 && 0 < b && c = 0) || (a = 0 && b = 0 && 0 < c)

/-- Bounded search for a stacking sequence on `P₃` (moves 0→1, 1→0, 1→2, 2→1). -/
def path_graph_three_stk : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, a, b, c => path_graph_three_stacked a b c
  | k + 1, a, b, c => path_graph_three_stacked a b c ||
      (2 ≤ a && path_graph_three_stk k (a - 2) (b + 1) c) ||
      (2 ≤ b && path_graph_three_stk k (a + 1) (b - 2) c) ||
      (2 ≤ b && path_graph_three_stk k a (b - 2) (c + 1)) ||
      (2 ≤ c && path_graph_three_stk k a (b + 1) (c - 2))

/-- No configuration reachable on `P₃` is stacked (fuel bounds the number of steps). -/
def path_graph_three_dead : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, a, b, c => !path_graph_three_stacked a b c && a < 2 && b < 2 && c < 2
  | k + 1, a, b, c => !path_graph_three_stacked a b c &&
      (a < 2 || path_graph_three_dead k (a - 2) (b + 1) c) &&
      (b < 2 || path_graph_three_dead k (a + 1) (b - 2) c) &&
      (b < 2 || path_graph_three_dead k a (b - 2) (c + 1)) &&
      (c < 2 || path_graph_three_dead k a (b + 1) (c - 2))

theorem path_graph_three_adj_iff (u v : Fin 3) :
    (SimpleGraph.pathGraph 3).Adj u v ↔
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by
  rw [SimpleGraph.pathGraph_adj]
  fin_cases u <;> fin_cases v <;> decide

theorem path_graph_three_stacked_iff (c : Fin 3 → ℕ) :
    path_graph_three_stacked (c 0) (c 1) (c 2) = true ↔ ∃ v, 0 < c v ∧ ∀ w, w ≠ v → c w = 0 := by
  simp only [path_graph_three_stacked, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((⟨⟨h0, h1⟩, h2⟩ | ⟨⟨h0, h1⟩, h2⟩) | ⟨⟨h0, h1⟩, h2⟩)
    · exact ⟨0, h0, fun w hw => by fin_cases w <;> simp_all⟩
    · exact ⟨1, h1, fun w hw => by fin_cases w <;> simp_all⟩
    · exact ⟨2, h2, fun w hw => by fin_cases w <;> simp_all⟩
  · rintro ⟨v, hv, hw⟩
    fin_cases v
    · exact Or.inl (Or.inl ⟨⟨hv, hw 1 (by decide)⟩, hw 2 (by decide)⟩)
    · exact Or.inl (Or.inr ⟨⟨hw 0 (by decide), hv⟩, hw 2 (by decide)⟩)
    · exact Or.inr ⟨⟨hw 0 (by decide), hw 1 (by decide)⟩, hv⟩

theorem path_graph_three_step_iff (c d : Fin 3 → ℕ) :
    graph_pebbling_step (SimpleGraph.pathGraph 3) c d ↔
      (2 ≤ c 0 ∧ d = ![c 0 - 2, c 1 + 1, c 2]) ∨ (2 ≤ c 1 ∧ d = ![c 0 + 1, c 1 - 2, c 2]) ∨
      (2 ≤ c 1 ∧ d = ![c 0, c 1 - 2, c 2 + 1]) ∨ (2 ≤ c 2 ∧ d = ![c 0, c 1 + 1, c 2 - 2]) := by
  constructor
  · rintro ⟨u, v, huv, hu, rfl⟩
    rw [path_graph_three_adj_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine Or.inl ⟨hu, ?_⟩
      funext i; fin_cases i <;> simp
    · refine Or.inr (Or.inl ⟨hu, ?_⟩)
      funext i; fin_cases i <;> simp
    · refine Or.inr (Or.inr (Or.inl ⟨hu, ?_⟩))
      funext i; fin_cases i <;> simp
    · refine Or.inr (Or.inr (Or.inr ⟨hu, ?_⟩))
      funext i; fin_cases i <;> simp
  · rintro (⟨hu, rfl⟩ | ⟨hu, rfl⟩ | ⟨hu, rfl⟩ | ⟨hu, rfl⟩)
    · refine ⟨0, 1, (path_graph_three_adj_iff _ _).2 (by decide), hu, ?_⟩
      funext i; fin_cases i <;> simp
    · refine ⟨1, 0, (path_graph_three_adj_iff _ _).2 (by decide), hu, ?_⟩
      funext i; fin_cases i <;> simp
    · refine ⟨1, 2, (path_graph_three_adj_iff _ _).2 (by decide), hu, ?_⟩
      funext i; fin_cases i <;> simp
    · refine ⟨2, 1, (path_graph_three_adj_iff _ _).2 (by decide), hu, ?_⟩
      funext i; fin_cases i <;> simp

theorem path_graph_three_stk_sound (k : ℕ) (c : Fin 3 → ℕ)
    (h : path_graph_three_stk k (c 0) (c 1) (c 2) = true) :
    graph_config_stackable (SimpleGraph.pathGraph 3) c := by
  induction k generalizing c with
  | zero =>
    obtain ⟨v, hv, hw⟩ := (path_graph_three_stacked_iff c).1 h
    exact ⟨c, Relation.ReflTransGen.refl, v, hv, hw⟩
  | succ k ih =>
    have back : ∀ d, graph_pebbling_step (SimpleGraph.pathGraph 3) c d →
        path_graph_three_stk k (d 0) (d 1) (d 2) = true →
        graph_config_stackable (SimpleGraph.pathGraph 3) c := by
      intro d hd hk
      obtain ⟨e, he, hst⟩ := ih d hk
      exact ⟨e, Relation.ReflTransGen.head hd he, hst⟩
    simp only [path_graph_three_stk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (((h | ⟨ha, h⟩) | ⟨hb, h⟩) | ⟨hb, h⟩) | ⟨hc, h⟩
    · obtain ⟨v, hv, hw⟩ := (path_graph_three_stacked_iff c).1 h
      exact ⟨c, Relation.ReflTransGen.refl, v, hv, hw⟩
    · exact back _ ((path_graph_three_step_iff _ _).2 (Or.inl ⟨ha, rfl⟩)) (by simpa using h)
    · exact back _ ((path_graph_three_step_iff _ _).2 (Or.inr (Or.inl ⟨hb, rfl⟩))) (by simpa using h)
    · exact back _ ((path_graph_three_step_iff _ _).2 (Or.inr (Or.inr (Or.inl ⟨hb, rfl⟩))))
        (by simpa using h)
    · exact back _ ((path_graph_three_step_iff _ _).2 (Or.inr (Or.inr (Or.inr ⟨hc, rfl⟩))))
        (by simpa using h)

theorem path_graph_three_dead_sound (k : ℕ) (c : Fin 3 → ℕ)
    (h : path_graph_three_dead k (c 0) (c 1) (c 2) = true) :
    ¬ graph_config_stackable (SimpleGraph.pathGraph 3) c := by
  rintro ⟨e, he, hst⟩
  induction he using Relation.ReflTransGen.head_induction_on generalizing k with
  | refl =>
    cases k <;>
    · simp only [path_graph_three_dead, Bool.and_eq_true, Bool.not_eq_true'] at h
      have := (path_graph_three_stacked_iff _).2 hst
      simp_all
  | head hd _ ih =>
    rename_i c c'
    cases k with
    | zero =>
      simp only [path_graph_three_dead, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases (path_graph_three_step_iff _ _).1 hd with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;>
        omega
    | succ k =>
      simp only [path_graph_three_dead, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨-, h0⟩, h1⟩, h2⟩, h3⟩ := h
      rcases (path_graph_three_step_iff _ _).1 hd with ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩
      · exact ih k (by simpa using h0.resolve_left (by omega))
      · exact ih k (by simpa using h1.resolve_left (by omega))
      · exact ih k (by simpa using h2.resolve_left (by omega))
      · exact ih k (by simpa using h3.resolve_left (by omega))

theorem path_graph_three_stk_seven :
    ∀ a ≤ 7, ∀ b ≤ 7 - a, path_graph_three_stk 7 a b (7 - a - b) = true := by
  decide

theorem path_graph_three_dead_examples :
    path_graph_three_dead 2 1 0 1 = true ∧ path_graph_three_dead 3 1 1 1 = true ∧
      path_graph_three_dead 4 3 0 1 = true ∧ path_graph_three_dead 5 3 1 1 = true ∧
      path_graph_three_dead 6 5 0 1 = true := by
  decide

theorem path_graph_three_stacking_number : graph_stacking_number (SimpleGraph.pathGraph 3) = 7 := by
  have hvec : ∀ c : Fin 3 → ℕ, c = ![c 0, c 1, c 2] := fun c => by
    funext i; fin_cases i <;> rfl
  have h7 : 7 ∈ {t : ℕ | 2 ≤ t ∧ ∀ c : Fin 3 → ℕ, ∑ v, c v = t →
      graph_config_stackable (SimpleGraph.pathGraph 3) c} := by
    refine ⟨by norm_num, fun c hc => ?_⟩
    rw [Fin.sum_univ_three] at hc
    apply path_graph_three_stk_sound 7
    have := path_graph_three_stk_seven (c 0) (by omega) (c 1) (by omega)
    rwa [show 7 - c 0 - c 1 = c 2 by omega] at this
  have hdead : ∀ t, 2 ≤ t → t < 7 → ∃ c : Fin 3 → ℕ, ∑ v, c v = t ∧
      ¬ graph_config_stackable (SimpleGraph.pathGraph 3) c := by
    obtain ⟨d2, d3, d4, d5, d6⟩ := path_graph_three_dead_examples
    intro t ht2 ht7
    interval_cases t
    · exact ⟨![1, 0, 1], by decide, path_graph_three_dead_sound 2 _ d2⟩
    · exact ⟨![1, 1, 1], by decide, path_graph_three_dead_sound 3 _ d3⟩
    · exact ⟨![3, 0, 1], by decide, path_graph_three_dead_sound 4 _ d4⟩
    · exact ⟨![3, 1, 1], by decide, path_graph_three_dead_sound 5 _ d5⟩
    · exact ⟨![5, 0, 1], by decide, path_graph_three_dead_sound 6 _ d6⟩
  unfold graph_stacking_number
  apply le_antisymm (Nat.sInf_le h7)
  refine le_csInf ⟨7, h7⟩ fun t ⟨ht2, hall⟩ => ?_
  by_contra hlt
  obtain ⟨c, hc, hns⟩ := hdead t ht2 (by omega)
  exact hns (hall c hc)

theorem path_graph_three_degree [DecidableRel (SimpleGraph.pathGraph 3).Adj] (v : Fin 3) :
    (SimpleGraph.pathGraph 3).degree v = if v = 1 then 2 else 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (SimpleGraph.pathGraph 3).neighborFinset v =
      Finset.univ.filter (fun w => (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0) ∨ (v = 1 ∧ w = 2) ∨
        (v = 2 ∧ w = 1)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      path_graph_three_adj_iff]
  rw [this]
  fin_cases v <;> decide

theorem path_graph_three_tree_estimate [DecidableRel (SimpleGraph.pathGraph 3).Adj] :
    simple_graph_tree_estimate (SimpleGraph.pathGraph 3) = 7 := by
  unfold simple_graph_tree_estimate
  simp only [path_graph_three_degree]
  have hd01 : (SimpleGraph.pathGraph 3).dist 0 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2 ((path_graph_three_adj_iff _ _).2 (by decide))
  have hd21 : (SimpleGraph.pathGraph 3).dist 2 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2 ((path_graph_three_adj_iff _ _).2 (by decide))
  have h : ∀ r : Fin 3,
      (∑ v ∈ Finset.univ.filter (fun v : Fin 3 => v = r ∨ 1 < if v = 1 then 2 else 1),
        (if v = 1 then 2 else 1) * 2 ^ (SimpleGraph.pathGraph 3).dist r v) +
        (Finset.univ.filter (fun v : Fin 3 => v ≠ r ∧ (if v = 1 then 2 else 1) = 1)).card =
      if r = 1 then 4 else 6 := by
    intro r
    fin_cases r <;> dsimp only <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · rw [show Finset.univ.filter (fun v : Fin 3 => v = 0 ∨ 1 < if v = 1 then 2 else 1) = {0, 1}
        by decide]
      rw [Finset.sum_pair (by decide), SimpleGraph.dist_self, hd01]
      decide
    · rw [show Finset.univ.filter (fun v : Fin 3 => v = 1 ∨ 1 < if v = 1 then 2 else 1) = {1}
        by decide]
      rw [Finset.sum_singleton, SimpleGraph.dist_self]
      decide
    · rw [show Finset.univ.filter (fun v : Fin 3 => v = 2 ∨ 1 < if v = 1 then 2 else 1) = {2, 1}
        by decide]
      rw [Finset.sum_pair (by decide), SimpleGraph.dist_self, hd21]
      decide
  simp only [h]
  decide

theorem path_graph_three_stacking_number_eq_tree_estimate
    [DecidableRel (SimpleGraph.pathGraph 3).Adj] :
    graph_stacking_number (SimpleGraph.pathGraph 3) =
      simple_graph_tree_estimate (SimpleGraph.pathGraph 3) := by
  rw [path_graph_three_stacking_number, path_graph_three_tree_estimate]
