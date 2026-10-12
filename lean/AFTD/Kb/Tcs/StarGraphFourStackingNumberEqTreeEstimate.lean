import AFTD.Prelude
import AFTD.Kb.Tcs.GraphStackingNumber
import AFTD.Kb.Tcs.SimpleGraphTreeEstimate
import AFTD.Kb.Tcs.GraphPebblingStep
import AFTD.Kb.Tcs.GraphConfigStackable

/-!
# star_graph_four_stacking_number_eq_tree_estimate

Topic: graphs   Node: d2e1c8476e97

Provenance: original. Related work: arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Conjecture 5.6, checked for the star K₁,₃ (Mathlib starGraph on Fin 4); the paper proves stack(T) ≥ estim(T) in general (Theorem 5.2) and equality under its Almost Stacked Hypothesis.

Conjecture 5.6 (OP-144) holds for the star K₁,₃ (center 0, leaves 1, 2, 3), the smallest tree that is not a path: stack(K₁,₃) = estim(K₁,₃) = 10.
-/

/-- Stacked quadruple on `K₁,₃` (center `0`, leaves `1, 2, 3`). -/
def star_graph_four_stacked (a b c d : ℕ) : Bool :=
  (0 < a && b = 0 && c = 0 && d = 0) || (a = 0 && 0 < b && c = 0 && d = 0) ||
    (a = 0 && b = 0 && 0 < c && d = 0) || (a = 0 && b = 0 && c = 0 && 0 < d)

/-- Bounded search for a stacking sequence on `K₁,₃`. -/
def star_graph_four_stk : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, a, b, c, d => star_graph_four_stacked a b c d
  | k + 1, a, b, c, d => star_graph_four_stacked a b c d ||
      (2 ≤ a && star_graph_four_stk k (a - 2) (b + 1) c d) ||
      (2 ≤ a && star_graph_four_stk k (a - 2) b (c + 1) d) ||
      (2 ≤ a && star_graph_four_stk k (a - 2) b c (d + 1)) ||
      (2 ≤ b && star_graph_four_stk k (a + 1) (b - 2) c d) ||
      (2 ≤ c && star_graph_four_stk k (a + 1) b (c - 2) d) ||
      (2 ≤ d && star_graph_four_stk k (a + 1) b c (d - 2))

/-- No configuration reachable on `K₁,₃` is stacked (fuel bounds the number of steps). -/
def star_graph_four_dead : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, a, b, c, d => !star_graph_four_stacked a b c d && a < 2 && b < 2 && c < 2 && d < 2
  | k + 1, a, b, c, d => !star_graph_four_stacked a b c d &&
      (a < 2 || star_graph_four_dead k (a - 2) (b + 1) c d) &&
      (a < 2 || star_graph_four_dead k (a - 2) b (c + 1) d) &&
      (a < 2 || star_graph_four_dead k (a - 2) b c (d + 1)) &&
      (b < 2 || star_graph_four_dead k (a + 1) (b - 2) c d) &&
      (c < 2 || star_graph_four_dead k (a + 1) b (c - 2) d) &&
      (d < 2 || star_graph_four_dead k (a + 1) b c (d - 2))

theorem star_graph_four_stacked_iff (c : Fin 4 → ℕ) :
    star_graph_four_stacked (c 0) (c 1) (c 2) (c 3) = true ↔
      ∃ v, 0 < c v ∧ ∀ w, w ≠ v → c w = 0 := by
  simp only [star_graph_four_stacked, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (((⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ | ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩) | ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩) |
      ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩)
    · exact ⟨0, h0, fun w hw => by fin_cases w <;> simp_all⟩
    · exact ⟨1, h1, fun w hw => by fin_cases w <;> simp_all⟩
    · exact ⟨2, h2, fun w hw => by fin_cases w <;> simp_all⟩
    · exact ⟨3, h3, fun w hw => by fin_cases w <;> simp_all⟩
  · rintro ⟨v, hv, hw⟩
    fin_cases v
    · exact Or.inl (Or.inl (Or.inl ⟨⟨⟨hv, hw 1 (by decide)⟩, hw 2 (by decide)⟩, hw 3 (by decide)⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨⟨⟨hw 0 (by decide), hv⟩, hw 2 (by decide)⟩, hw 3 (by decide)⟩))
    · exact Or.inl (Or.inr ⟨⟨⟨hw 0 (by decide), hw 1 (by decide)⟩, hv⟩, hw 3 (by decide)⟩)
    · exact Or.inr ⟨⟨⟨hw 0 (by decide), hw 1 (by decide)⟩, hw 2 (by decide)⟩, hv⟩

theorem star_graph_four_step_iff (c e : Fin 4 → ℕ) :
    graph_pebbling_step (SimpleGraph.starGraph (0 : Fin 4)) c e ↔
      (2 ≤ c 0 ∧ e = ![c 0 - 2, c 1 + 1, c 2, c 3]) ∨
      (2 ≤ c 0 ∧ e = ![c 0 - 2, c 1, c 2 + 1, c 3]) ∨
      (2 ≤ c 0 ∧ e = ![c 0 - 2, c 1, c 2, c 3 + 1]) ∨
      (2 ≤ c 1 ∧ e = ![c 0 + 1, c 1 - 2, c 2, c 3]) ∨
      (2 ≤ c 2 ∧ e = ![c 0 + 1, c 1, c 2 - 2, c 3]) ∨
      (2 ≤ c 3 ∧ e = ![c 0 + 1, c 1, c 2, c 3 - 2]) := by
  constructor
  · rintro ⟨u, v, huv, hu, rfl⟩
    rw [SimpleGraph.starGraph_adj] at huv
    fin_cases u <;> fin_cases v <;> simp at huv
    · exact Or.inl ⟨hu, by funext i; fin_cases i <;> simp⟩
    · exact Or.inr (Or.inl ⟨hu, by funext i; fin_cases i <;> simp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hu, by funext i; fin_cases i <;> simp⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, by funext i; fin_cases i <;> simp⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, by funext i; fin_cases i <;> simp⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hu, by funext i; fin_cases i <;> simp⟩))))
  · have adj : ∀ u v : Fin 4, u ≠ v → (u = 0 ∨ v = 0) →
        (SimpleGraph.starGraph (0 : Fin 4)).Adj u v := fun u v h1 h2 =>
      SimpleGraph.starGraph_adj.2 ⟨h1, h2⟩
    rintro (⟨hu, rfl⟩ | ⟨hu, rfl⟩ | ⟨hu, rfl⟩ | ⟨hu, rfl⟩ | ⟨hu, rfl⟩ | ⟨hu, rfl⟩)
    · exact ⟨0, 1, adj _ _ (by decide) (by decide), hu, by funext i; fin_cases i <;> simp⟩
    · exact ⟨0, 2, adj _ _ (by decide) (by decide), hu, by funext i; fin_cases i <;> simp⟩
    · exact ⟨0, 3, adj _ _ (by decide) (by decide), hu, by funext i; fin_cases i <;> simp⟩
    · exact ⟨1, 0, adj _ _ (by decide) (by decide), hu, by funext i; fin_cases i <;> simp⟩
    · exact ⟨2, 0, adj _ _ (by decide) (by decide), hu, by funext i; fin_cases i <;> simp⟩
    · exact ⟨3, 0, adj _ _ (by decide) (by decide), hu, by funext i; fin_cases i <;> simp⟩

theorem star_graph_four_stk_sound (k : ℕ) (c : Fin 4 → ℕ)
    (h : star_graph_four_stk k (c 0) (c 1) (c 2) (c 3) = true) :
    graph_config_stackable (SimpleGraph.starGraph (0 : Fin 4)) c := by
  induction k generalizing c with
  | zero =>
    obtain ⟨v, hv, hw⟩ := (star_graph_four_stacked_iff c).1 h
    exact ⟨c, Relation.ReflTransGen.refl, v, hv, hw⟩
  | succ k ih =>
    have back : ∀ e, graph_pebbling_step (SimpleGraph.starGraph (0 : Fin 4)) c e →
        star_graph_four_stk k (e 0) (e 1) (e 2) (e 3) = true →
        graph_config_stackable (SimpleGraph.starGraph (0 : Fin 4)) c := by
      intro e he hk
      obtain ⟨f, hf, hst⟩ := ih e hk
      exact ⟨f, Relation.ReflTransGen.head he hf, hst⟩
    simp only [star_graph_four_stk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (((((h | ⟨h0, h⟩) | ⟨h0, h⟩) | ⟨h0, h⟩) | ⟨h0, h⟩) | ⟨h0, h⟩) | ⟨h0, h⟩
    · obtain ⟨v, hv, hw⟩ := (star_graph_four_stacked_iff c).1 h
      exact ⟨c, Relation.ReflTransGen.refl, v, hv, hw⟩
    · exact back _ ((star_graph_four_step_iff _ _).2 (Or.inl ⟨h0, rfl⟩)) (by simpa using h)
    · exact back _ ((star_graph_four_step_iff _ _).2 (Or.inr (Or.inl ⟨h0, rfl⟩))) (by simpa using h)
    · exact back _ ((star_graph_four_step_iff _ _).2 (Or.inr (Or.inr (Or.inl ⟨h0, rfl⟩))))
        (by simpa using h)
    · exact back _ ((star_graph_four_step_iff _ _).2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, rfl⟩)))))
        (by simpa using h)
    · exact back _ ((star_graph_four_step_iff _ _).2
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, rfl⟩)))))) (by simpa using h)
    · exact back _ ((star_graph_four_step_iff _ _).2
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, rfl⟩)))))) (by simpa using h)

theorem star_graph_four_dead_sound (k : ℕ) (c : Fin 4 → ℕ)
    (h : star_graph_four_dead k (c 0) (c 1) (c 2) (c 3) = true) :
    ¬ graph_config_stackable (SimpleGraph.starGraph (0 : Fin 4)) c := by
  rintro ⟨e, he, hst⟩
  induction he using Relation.ReflTransGen.head_induction_on generalizing k with
  | refl =>
    cases k <;>
    · simp only [star_graph_four_dead, Bool.and_eq_true, Bool.not_eq_true'] at h
      have := (star_graph_four_stacked_iff _).2 hst
      simp_all
  | head hd _ ih =>
    cases k with
    | zero =>
      simp only [star_graph_four_dead, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases (star_graph_four_step_iff _ _).1 hd with
        ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> omega
    | succ k =>
      simp only [star_graph_four_dead, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨-, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
      rcases (star_graph_four_step_iff _ _).1 hd with
        ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩
      · exact ih k (by simpa using h0.resolve_left (by omega))
      · exact ih k (by simpa using h1.resolve_left (by omega))
      · exact ih k (by simpa using h2.resolve_left (by omega))
      · exact ih k (by simpa using h3.resolve_left (by omega))
      · exact ih k (by simpa using h4.resolve_left (by omega))
      · exact ih k (by simpa using h5.resolve_left (by omega))

theorem star_graph_four_stk_ten :
    ∀ a ≤ 10, ∀ b ≤ 10 - a, ∀ c ≤ 10 - a - b,
      star_graph_four_stk 10 a b c (10 - a - b - c) = true := by
  decide

theorem star_graph_four_dead_examples :
    star_graph_four_dead 2 0 0 1 1 = true ∧ star_graph_four_dead 3 0 1 1 1 = true ∧
      star_graph_four_dead 4 0 0 1 3 = true ∧ star_graph_four_dead 5 0 1 1 3 = true ∧
      star_graph_four_dead 6 0 0 1 5 = true ∧ star_graph_four_dead 7 0 1 1 5 = true ∧
      star_graph_four_dead 8 1 1 1 5 = true ∧ star_graph_four_dead 9 0 1 1 7 = true := by
  decide

theorem star_graph_four_stacking_number :
    graph_stacking_number (SimpleGraph.starGraph (0 : Fin 4)) = 10 := by
  have h10 : 10 ∈ {t : ℕ | 2 ≤ t ∧ ∀ c : Fin 4 → ℕ, ∑ v, c v = t →
      graph_config_stackable (SimpleGraph.starGraph (0 : Fin 4)) c} := by
    refine ⟨by norm_num, fun c hc => ?_⟩
    rw [Fin.sum_univ_four] at hc
    apply star_graph_four_stk_sound 10
    have := star_graph_four_stk_ten (c 0) (by omega) (c 1) (by omega) (c 2) (by omega)
    rwa [show 10 - c 0 - c 1 - c 2 = c 3 by omega] at this
  have hdead : ∀ t, 2 ≤ t → t < 10 → ∃ c : Fin 4 → ℕ, ∑ v, c v = t ∧
      ¬ graph_config_stackable (SimpleGraph.starGraph (0 : Fin 4)) c := by
    obtain ⟨d2, d3, d4, d5, d6, d7, d8, d9⟩ := star_graph_four_dead_examples
    intro t ht2 ht10
    interval_cases t
    · exact ⟨![0, 0, 1, 1], by decide, star_graph_four_dead_sound 2 _ d2⟩
    · exact ⟨![0, 1, 1, 1], by decide, star_graph_four_dead_sound 3 _ d3⟩
    · exact ⟨![0, 0, 1, 3], by decide, star_graph_four_dead_sound 4 _ d4⟩
    · exact ⟨![0, 1, 1, 3], by decide, star_graph_four_dead_sound 5 _ d5⟩
    · exact ⟨![0, 0, 1, 5], by decide, star_graph_four_dead_sound 6 _ d6⟩
    · exact ⟨![0, 1, 1, 5], by decide, star_graph_four_dead_sound 7 _ d7⟩
    · exact ⟨![1, 1, 1, 5], by decide, star_graph_four_dead_sound 8 _ d8⟩
    · exact ⟨![0, 1, 1, 7], by decide, star_graph_four_dead_sound 9 _ d9⟩
  unfold graph_stacking_number
  apply le_antisymm (Nat.sInf_le h10)
  refine le_csInf ⟨10, h10⟩ fun t ⟨ht2, hall⟩ => ?_
  by_contra hlt
  obtain ⟨c, hc, hns⟩ := hdead t ht2 (by omega)
  exact hns (hall c hc)

theorem star_graph_four_degree (v : Fin 4) :
    (SimpleGraph.starGraph (0 : Fin 4)).degree v = if v = 0 then 3 else 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (SimpleGraph.starGraph (0 : Fin 4)).neighborFinset v =
      Finset.univ.filter (fun w => v ≠ w ∧ (v = 0 ∨ w = 0)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.starGraph_adj]
  rw [this]
  fin_cases v <;> decide

theorem star_graph_four_tree_estimate :
    simple_graph_tree_estimate (SimpleGraph.starGraph (0 : Fin 4)) = 10 := by
  unfold simple_graph_tree_estimate
  simp only [star_graph_four_degree]
  have hd : ∀ v : Fin 4, v ≠ 0 → (SimpleGraph.starGraph (0 : Fin 4)).dist v 0 = 1 := fun v hv =>
    SimpleGraph.dist_eq_one_iff_adj.2 (SimpleGraph.starGraph_adj.2 ⟨hv, Or.inr rfl⟩)
  have h : ∀ r : Fin 4,
      (∑ v ∈ Finset.univ.filter (fun v : Fin 4 => v = r ∨ 1 < if v = 0 then 3 else 1),
        (if v = 0 then 3 else 1) * 2 ^ (SimpleGraph.starGraph (0 : Fin 4)).dist r v) +
        (Finset.univ.filter (fun v : Fin 4 => v ≠ r ∧ (if v = 0 then 3 else 1) = 1)).card =
      if r = 0 then 6 else 9 := by
    intro r
    fin_cases r <;> dsimp only <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · rw [show Finset.univ.filter (fun v : Fin 4 => v = 0 ∨ 1 < if v = 0 then 3 else 1) = {0}
        by decide]
      rw [Finset.sum_singleton, SimpleGraph.dist_self]
      decide
    · rw [show Finset.univ.filter (fun v : Fin 4 => v = 1 ∨ 1 < if v = 0 then 3 else 1) = {1, 0}
        by decide]
      rw [Finset.sum_pair (by decide), SimpleGraph.dist_self, hd 1 (by decide)]
      decide
    · rw [show Finset.univ.filter (fun v : Fin 4 => v = 2 ∨ 1 < if v = 0 then 3 else 1) = {2, 0}
        by decide]
      rw [Finset.sum_pair (by decide), SimpleGraph.dist_self, hd 2 (by decide)]
      decide
    · rw [show Finset.univ.filter (fun v : Fin 4 => v = 3 ∨ 1 < if v = 0 then 3 else 1) = {3, 0}
        by decide]
      rw [Finset.sum_pair (by decide), SimpleGraph.dist_self, hd 3 (by decide)]
      decide
  simp only [h]
  decide

theorem star_graph_four_stacking_number_eq_tree_estimate :
    graph_stacking_number (SimpleGraph.starGraph (0 : Fin 4)) =
      simple_graph_tree_estimate (SimpleGraph.starGraph (0 : Fin 4)) := by
  rw [star_graph_four_stacking_number, star_graph_four_tree_estimate]
