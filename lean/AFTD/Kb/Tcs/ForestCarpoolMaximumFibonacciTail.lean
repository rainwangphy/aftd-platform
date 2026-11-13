import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolForestEdgeSequence
import AFTD.Kb.Tcs.ForestCarpoolFinalOneSidedFibonacciTail
import AFTD.Kb.Tcs.MaxVertexDiscrepancy
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope
import AFTD.Kb.Tcs.ForestCarpoolComponentCoinLocality
import AFTD.Kb.Tcs.ValidCarpoolEdgeSequence
import AFTD.Kb.Tcs.ForestCarpoolFinalDiscrepancy
import AFTD.Kb.Tcs.CarpoolStep

/-!
# forest_carpool_maximum_fibonacci_tail

Topic: online_algorithms   Node: edfe3a266275

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

For a forest arrival sequence, the probability that any vertex at any prefix has absolute discrepancy at least D is at most four times the number of edges times the Fibonacci tail envelope.
-/

namespace ForestCarpoolMax

open ForestCarpoolLocal

theorem foldl_aux (n : ℕ) : ∀ (es : List (Fin n × Fin n)) (cs : List Bool) (d : Fin n → ℤ),
    (es.zip (carpool_greedy_orientations.aux n es cs d)).foldl
      (fun d (e, b) => carpool_step n d e b) d = G n es cs d := by
  intro es
  induction es with
  | nil => intro cs d; simp [carpool_greedy_orientations.aux, G]
  | cons e es ih =>
    intro cs d
    cases cs with
    | nil => simp [carpool_greedy_orientations.aux, G]
    | cons c cs =>
      simp only [carpool_greedy_orientations.aux, List.zip_cons_cons, List.foldl_cons, G]
      exact ih cs _

theorem take_zip_aux (n : ℕ) : ∀ (es : List (Fin n × Fin n)) (cs : List Bool)
    (d : Fin n → ℤ) (t : ℕ),
    (es.zip (carpool_greedy_orientations.aux n es cs d)).take t =
      (es.take t).zip (carpool_greedy_orientations.aux n (es.take t) (cs.take t) d) := by
  intro es
  induction es with
  | nil => intro cs d t; simp [carpool_greedy_orientations.aux]
  | cons e es ih =>
    intro cs d t
    cases cs with
    | nil =>
      cases t <;> simp [carpool_greedy_orientations.aux]
    | cons c cs =>
      cases t with
      | zero => simp [carpool_greedy_orientations.aux]
      | succ t =>
        simp only [carpool_greedy_orientations.aux, List.zip_cons_cons, List.take_succ_cons]
        rw [ih]

theorem G_append' (n : ℕ) (e : Fin n × Fin n) (c : Bool) :
    ∀ (es : List (Fin n × Fin n)) (cs : List Bool) (d : Fin n → ℤ), cs.length = es.length →
    G n (es ++ [e]) (cs ++ [c]) d = carpool_step n (G n es cs d) e (gbit (G n es cs d) e c) := by
  intro es
  induction es with
  | nil =>
    intro cs d h
    cases cs with
    | nil => simp [G]
    | cons _ _ => simp at h
  | cons e' es ih =>
    intro cs d h
    cases cs with
    | nil => simp at h
    | cons c' cs =>
      simp only [List.cons_append, G]
      exact ih cs _ (by simpa using h)

theorem G_nil (n : ℕ) (cs : List Bool) (d : Fin n → ℤ) : G n [] cs d = d := by
  cases cs <;> rfl

theorem foldl_max_le (D : ℕ) : ∀ (l : List ℕ) (acc : ℕ), D ≤ l.foldl max acc →
    D ≤ acc ∨ ∃ x ∈ l, D ≤ x := by
  intro l
  induction l with
  | nil => intro acc h; exact Or.inl h
  | cons x l ih =>
    intro acc h
    rcases ih _ h with h1 | ⟨y, hy, h2⟩
    · rcases le_max_iff.mp h1 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨x, by simp, h3⟩
    · exact Or.inr ⟨y, by simp [hy], h2⟩

/-- if some prefix discrepancy is large, it is large right after an edge at that vertex -/
theorem last_touch (n : ℕ) (es : List (Fin n × Fin n)) (cs : List Bool)
    (hcs : cs.length = es.length) (D : ℕ) (hD : 1 ≤ D) :
    ∀ t, t ≤ es.length → ∀ w, D ≤ (G n (es.take t) (cs.take t) (fun _ => 0) w).natAbs →
    ∃ j, ∃ hj : j < es.length, (w = (es[j]).1 ∨ w = (es[j]).2) ∧
      D ≤ (G n (es.take (j + 1)) (cs.take (j + 1)) (fun _ => 0) w).natAbs := by
  intro t
  induction t with
  | zero => intro _ w h; simp [G_nil] at h; omega
  | succ t ih =>
    intro ht w h
    by_cases hw : w = (es[t]'(by omega)).1 ∨ w = (es[t]'(by omega)).2
    · exact ⟨t, by omega, hw, h⟩
    · apply ih (by omega) w
      have hes : es.take (t + 1) = es.take t ++ [es[t]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
      have hcs' : cs.take (t + 1) = cs.take t ++ [cs[t]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hes, hcs', G_append' n _ _ _ _ _ (by simp [hcs])] at h
      push Not at hw
      simpa [carpool_step, hw.1, hw.2] using h

theorem gbit_neg {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (c : Bool) :
    gbit (fun x => -d x) e (!c) = !(gbit d e c) := by
  unfold gbit
  dsimp only
  cases c <;> split_ifs <;> first | rfl | (exfalso; omega)

theorem step_neg {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (b : Bool) :
    carpool_step n (fun x => -d x) e (!b) = fun x => -(carpool_step n d e b x) := by
  funext x
  unfold carpool_step
  cases b <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false] <;>
    split_ifs <;> ring

theorem G_neg (n : ℕ) : ∀ (es : List (Fin n × Fin n)) (cs : List Bool) (d : Fin n → ℤ),
    G n es (cs.map (!·)) (fun x => -d x) = fun x => -(G n es cs d x) := by
  intro es
  induction es with
  | nil => intro cs d; simp [G_nil]
  | cons e es ih =>
    intro cs d
    cases cs with
    | nil => rfl
    | cons c cs =>
      simp only [List.map_cons, G]
      rw [gbit_neg, step_neg, ih]

theorem card_comp_equiv'' {γ δ : Type} [Fintype γ] [Fintype δ] (Φ : γ ≃ δ) (f : δ → Prop)
    [DecidablePred f] :
    (Finset.univ.filter (fun p => f (Φ p))).card = (Finset.univ.filter f).card := by
  refine Finset.card_nbij' Φ Φ.symm ?_ ?_ (fun p _ => Φ.symm_apply_apply p)
    (fun p _ => Φ.apply_symm_apply p)
  · intro p hp; simpa using hp
  · intro p hp; simpa using hp

/-- split the coins into a prefix and a suffix -/
def splitEquiv (t T : ℕ) (h : t ≤ T) : (Fin T → Bool) ≃ (Fin t → Bool) × (Fin (T - t) → Bool) where
  toFun r := (fun i => r ⟨i, by omega⟩, fun j => r ⟨t + j, by omega⟩)
  invFun p := fun i => if hi : i.val < t then p.1 ⟨i, hi⟩ else p.2 ⟨i - t, by omega⟩
  left_inv r := by
    funext i
    by_cases hi : i.val < t
    · simp [hi]
    · simp only [hi, dite_false]; congr 1; ext; simp; omega
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    ext j
    · simp
    · simp

theorem marginal (t T : ℕ) (h : t ≤ T) (P : (Fin t → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun r : Fin T → Bool => P (fun i => r ⟨i, by omega⟩))).card =
      (Finset.univ.filter P).card * 2 ^ (T - t) := by
  rw [← card_comp_equiv'' (splitEquiv t T h).symm (fun r : Fin T → Bool =>
    P (fun i => r ⟨i, by omega⟩))]
  have : (Finset.univ.filter (fun p : (Fin t → Bool) × (Fin (T - t) → Bool) =>
      P (fun i => (splitEquiv t T h).symm p ⟨i, by omega⟩))) =
      (Finset.univ.filter P) ×ˢ Finset.univ := by
    ext ⟨p1, p2⟩
    simp [splitEquiv]
  rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]

theorem forest_take (n : ℕ) (es : List (Fin n × Fin n)) (t : ℕ)
    (hf : CarpoolForestEdgeSequence n es) : CarpoolForestEdgeSequence n (es.take t) := by
  obtain ⟨hv, hnd, hac⟩ := hf
  have hsub : ∀ x ∈ es.take t, x ∈ es := fun x hx => List.mem_of_mem_take hx
  refine ⟨fun x hx => hv x (hsub x hx), ?_, ?_⟩
  · rw [List.map_take]; exact hnd.sublist (List.take_sublist _ _)
  · refine hac.anti ?_
    intro x y hxy
    rw [SimpleGraph.fromEdgeSet_adj] at hxy ⊢
    obtain ⟨⟨e', he', hex⟩, hne⟩ := hxy
    exact ⟨⟨e', hsub e' he', hex⟩, hne⟩

/-- the one-sided bound for a prefix, with unused suffix coins, in counting form -/
theorem prefix_bound (n : ℕ) (es : List (Fin n × Fin n)) (hf : CarpoolForestEdgeSequence n es)
    (t : ℕ) (ht : t ≤ es.length) (w : Fin n) (D : ℕ) (hD : 1 ≤ D) (sgn : Bool) :
    ((Finset.univ.filter (fun r : Fin es.length → Bool =>
      (D : ℤ) ≤ (if sgn then 1 else -1) *
        G n (es.take t) ((List.ofFn r).take t) (fun _ => 0) w)).card : ℝ) ≤
      forest_carpool_tail_envelope D * 2 ^ es.length := by
  have hlen : (es.take t).length = t := by simp; omega
  -- restrict coins
  have hres : ∀ r : Fin es.length → Bool, (List.ofFn r).take t =
      List.ofFn (fun i : Fin (es.take t).length => r ⟨i, by omega⟩) := by
    intro r
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp
  have hcount := marginal (es.take t).length es.length (by omega)
    (fun r' => (D : ℤ) ≤ (if sgn then 1 else -1) *
      forest_carpool_final_discrepancy n (es.take t) r' w)
  have heq : (Finset.univ.filter (fun r : Fin es.length → Bool =>
      (D : ℤ) ≤ (if sgn then 1 else -1) *
        G n (es.take t) ((List.ofFn r).take t) (fun _ => 0) w)) =
      Finset.univ.filter (fun r : Fin es.length → Bool =>
        (D : ℤ) ≤ (if sgn then 1 else -1) * forest_carpool_final_discrepancy n (es.take t)
          (fun i => r ⟨i, by omega⟩) w) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [final_eq, hres]
  rw [heq, hcount]
  -- the prefix bound
  have hpre : ((Finset.univ.filter (fun r' : Fin (es.take t).length → Bool =>
      (D : ℤ) ≤ (if sgn then 1 else -1) *
        forest_carpool_final_discrepancy n (es.take t) r' w)).card : ℝ) ≤
      forest_carpool_tail_envelope D * 2 ^ (es.take t).length := by
    have hb := forest_carpool_final_one_sided_fibonacci_tail n (es.take t)
      (forest_take n es t hf) w D hD
    rw [div_le_iff₀ (by positivity)] at hb
    cases sgn
    · -- negative side: flip all coins
      let flip : (Fin (es.take t).length → Bool) ≃ (Fin (es.take t).length → Bool) :=
        { toFun := fun r i => !r i, invFun := fun r i => !r i,
          left_inv := fun r => by funext i; simp, right_inv := fun r => by funext i; simp }
      have hneg : ∀ r', forest_carpool_final_discrepancy n (es.take t) (flip r') w =
          - forest_carpool_final_discrepancy n (es.take t) r' w := by
        intro r'
        rw [final_eq, final_eq]
        have : List.ofFn (flip r') = (List.ofFn r').map (!·) := by
          rw [List.map_ofFn]; rfl
        rw [this]
        have := congrFun (G_neg n (es.take t) (List.ofFn r') (fun _ => 0)) w
        simpa using this
      rw [← card_comp_equiv'' flip] at hb
      simp only [hneg] at hb
      simp only [Bool.false_eq_true, if_false, neg_one_mul]
      exact hb
    · simp only [if_true, one_mul]
      exact hb
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_two]
  have hsplit : (2 : ℝ) ^ es.length = 2 ^ (es.take t).length * 2 ^ (es.length - (es.take t).length) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hpre (by positivity)

end ForestCarpoolMax

theorem forest_carpool_maximum_fibonacci_tail (n : ℕ)
    (edges : List (Fin n × Fin n)) (hf : CarpoolForestEdgeSequence n edges)
    (D : ℕ) (hD : 1 ≤ D) :
  (((Finset.univ.filter (fun r : Fin edges.length → Bool =>
    D ≤ carpool_max_discrepancy n edges
      (carpool_greedy_orientations n edges (List.ofFn r)))).card : ℝ) /
    (2 ^ edges.length : ℝ)) ≤ 4 * edges.length * forest_carpool_tail_envelope D := by
  classical
  open ForestCarpoolLocal ForestCarpoolMax in
  set T := edges.length with hT
  let ev : Fin T → Fin n → Bool → Finset (Fin T → Bool) := fun j w sgn =>
    Finset.univ.filter (fun r : Fin edges.length → Bool =>
      (D : ℤ) ≤ (if sgn then 1 else -1) *
        G n (edges.take (j + 1)) ((List.ofFn r).take (j + 1)) (fun _ => 0) w)
  have hsub : Finset.univ.filter (fun r : Fin edges.length → Bool =>
      D ≤ carpool_max_discrepancy n edges (carpool_greedy_orientations n edges (List.ofFn r))) ⊆
      Finset.univ.biUnion (fun j : Fin T =>
        ev j (edges[j]).1 true ∪ ev j (edges[j]).1 false ∪
        ev j (edges[j]).2 true ∪ ev j (edges[j]).2 false) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    unfold carpool_max_discrepancy carpool_discrepancies carpool_greedy_orientations at hr
    rcases foldl_max_le D _ 0 hr with h0 | ⟨x, hx, hDx⟩
    · omega
    obtain ⟨dv, hdv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdv
    rw [List.getElem_scanl, take_zip_aux, foldl_aux] at hDx
    unfold max_vertex_discrepancy at hDx
    obtain ⟨w, _, hw⟩ := (Finset.le_sup_iff (lt_of_lt_of_le (by decide : (⊥ : ℕ) < 1) hD)).mp hDx
    have hilen : i ≤ edges.length := by
      simp [List.length_scanl] at hi; omega
    obtain ⟨j, hj, hjw, hjD⟩ := last_touch n edges (List.ofFn r) (by simp) D hD i hilen w hw
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    refine ⟨⟨j, hj⟩, ?_⟩
    simp only [ev, Finset.mem_filter, Finset.mem_univ, true_and, if_true, if_false,
      Bool.false_eq_true, one_mul, neg_one_mul]
    have habs : (D : ℤ) ≤ G n (edges.take (j + 1)) ((List.ofFn r).take (j + 1)) (fun _ => 0) w ∨
        (D : ℤ) ≤ -G n (edges.take (j + 1)) ((List.ofFn r).take (j + 1)) (fun _ => 0) w := by
      omega
    rcases hjw with rfl | rfl <;> rcases habs with h | h <;> simp [h]
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hbound : ∀ j : Fin T, ((ev j (edges[j]).1 true ∪ ev j (edges[j]).1 false ∪
      ev j (edges[j]).2 true ∪ ev j (edges[j]).2 false).card : ℝ) ≤
      4 * (forest_carpool_tail_envelope D * 2 ^ edges.length) := by
    intro j
    have h1 : ((ev j (edges[j]).1 true).card : ℝ) ≤ forest_carpool_tail_envelope D * 2 ^ edges.length :=
      prefix_bound n edges hf (j + 1) j.2 (edges[j]).1 D hD true
    have h2 : ((ev j (edges[j]).1 false).card : ℝ) ≤ forest_carpool_tail_envelope D * 2 ^ edges.length :=
      prefix_bound n edges hf (j + 1) j.2 (edges[j]).1 D hD false
    have h3 : ((ev j (edges[j]).2 true).card : ℝ) ≤ forest_carpool_tail_envelope D * 2 ^ edges.length :=
      prefix_bound n edges hf (j + 1) j.2 (edges[j]).2 D hD true
    have h4 : ((ev j (edges[j]).2 false).card : ℝ) ≤ forest_carpool_tail_envelope D * 2 ^ edges.length :=
      prefix_bound n edges hf (j + 1) j.2 (edges[j]).2 D hD false
    have hu := Finset.card_union_le (ev j (edges[j]).1 true ∪ ev j (edges[j]).1 false ∪
      ev j (edges[j]).2 true) (ev j (edges[j]).2 false)
    have hu2 := Finset.card_union_le (ev j (edges[j]).1 true ∪ ev j (edges[j]).1 false)
      (ev j (edges[j]).2 true)
    have hu3 := Finset.card_union_le (ev j (edges[j]).1 true) (ev j (edges[j]).1 false)
    have : ((ev j (edges[j]).1 true ∪ ev j (edges[j]).1 false ∪
      ev j (edges[j]).2 true ∪ ev j (edges[j]).2 false).card : ℝ) ≤
      (ev j (edges[j]).1 true).card + (ev j (edges[j]).1 false).card +
      (ev j (edges[j]).2 true).card + (ev j (edges[j]).2 false).card := by
      exact_mod_cast (by omega)
    linarith
  have hsum : ((Finset.univ.filter (fun r : Fin edges.length → Bool =>
      D ≤ carpool_max_discrepancy n edges
        (carpool_greedy_orientations n edges (List.ofFn r)))).card : ℝ) ≤
      T * (4 * (forest_carpool_tail_envelope D * 2 ^ edges.length)) := by
    calc _ ≤ ((∑ j : Fin T, (ev j (edges[j]).1 true ∪ ev j (edges[j]).1 false ∪
          ev j (edges[j]).2 true ∪ ev j (edges[j]).2 false).card : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ = ∑ j : Fin T, ((ev j (edges[j]).1 true ∪ ev j (edges[j]).1 false ∪
          ev j (edges[j]).2 true ∪ ev j (edges[j]).2 false).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _j : Fin T, 4 * (forest_carpool_tail_envelope D * 2 ^ edges.length) :=
          Finset.sum_le_sum (fun j _ => hbound j)
      _ = _ := by simp
  rw [div_le_iff₀ (by positivity)]
  linarith
