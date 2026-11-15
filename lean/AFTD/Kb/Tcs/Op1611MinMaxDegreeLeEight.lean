import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphReconfigurationDiamGtMatching
import AFTD.Kb.Tcs.GraphMatchingNum
import AFTD.Kb.Tcs.SimpleGraphReconfigurationGraph
import AFTD.Kb.Tcs.GraphMatchingNumLeVertexCoverNum
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op_1611_min_max_degree_le_eight

Topic: graphs   Node: 52525b6e4448

Provenance: formalization of a published result. Source: arXiv:2611.17022 Theorem 4

The natural number 8 satisfies simple_graph_reconfiguration_diam_gt_matching 8.
-/

open Finset

namespace Op1611LeEight

/-- The 1-subdivision of the doubled K₅: `(i,i)` is `xᵢ`, `(i,j)` with `i ≠ j` is `y_ij`,
adjacent to `xᵢ` and `xⱼ`. -/
def G5 : SimpleGraph (Fin 5 × Fin 5) where
  Adj p q := (p.1 = p.2 ∧ q.1 ≠ q.2 ∧ (q.1 = p.1 ∨ q.2 = p.1)) ∨
    (q.1 = q.2 ∧ p.1 ≠ p.2 ∧ (p.1 = q.1 ∨ p.2 = q.1))
  symm := ⟨fun p q h => by tauto⟩
  loopless := ⟨fun p h => by rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> exact h2 h1⟩

instance op1611LeEight_G5_decAdj : DecidableRel G5.Adj := fun p q =>
  inferInstanceAs (Decidable ((p.1 = p.2 ∧ q.1 ≠ q.2 ∧ (q.1 = p.1 ∨ q.2 = p.1)) ∨
    (q.1 = q.2 ∧ p.1 ≠ p.2 ∧ (p.1 = q.1 ∨ p.2 = q.1))))

theorem G5_degree_le : ∀ p, G5.degree p ≤ 8 := by decide +kernel

theorem G5_degree_x : G5.degree (0, 0) = 8 := by decide +kernel

theorem G5_maxDegree : G5.maxDegree = 8 :=
  le_antisymm (G5.maxDegree_le_of_forall_degree_le 8 G5_degree_le)
    (G5_degree_x ▸ G5.degree_le_maxDegree _)

theorem G5_matching : graph_matching_num G5 ≤ 5 := by
  refine (graph_matching_num_le_vertex_cover_num G5).trans ?_
  have hc : G5.IsVertexCover {p | p.1 = p.2} := by
    intro p q h
    change _ ∨ _ at h
    rcases h with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  refine hc.vertexCoverNum_le.trans ?_
  have : ({p | p.1 = p.2} : Set (Fin 5 × Fin 5)) =
      ((Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 = p.2 : Finset _) : Set _) := by
    ext p; simp
  rw [this, Set.encard_coe_eq_coe_finsetCard]
  have h5 : (Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 = p.2).card = 5 := by decide
  rw [h5]; rfl

/-- Colouring α: `xᵢ ↦ aᵢ = i`, `y_ij ↦ bᵢ = 5 + i`. -/
def α5 : G5.Coloring (Fin 10) :=
  SimpleGraph.Coloring.mk
    (fun p => ⟨if p.1 = p.2 then p.1.val else 5 + p.1.val, by split <;> omega⟩)
    (by
      intro p q h heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      change _ ∨ _ at h
      rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      simp only [Fin.ext_iff, ne_eq] at h1 h2 h3 <;>
      split_ifs at hv <;> simp only [Fin.ext_iff] at * <;> omega)

/-- Colouring β: `xᵢ ↦ bᵢ = 5 + i`, `y_ij ↦ aⱼ = j`. -/
def β5 : G5.Coloring (Fin 10) :=
  SimpleGraph.Coloring.mk
    (fun p => ⟨if p.1 = p.2 then 5 + p.1.val else p.2.val, by split <;> omega⟩)
    (by
      intro p q h heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      change _ ∨ _ at h
      rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      simp only [Fin.ext_iff, ne_eq] at h1 h2 h3 <;>
      split_ifs at hv <;> simp only [Fin.ext_iff] at * <;> omega)

theorem α5_ne_β5 : ∀ p, α5 p ≠ β5 p := by decide +kernel

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {K : ℕ}

/-- Steps of a recolouring walk at which vertex `v` changes. -/
def steps {a b : G.Coloring (Fin K)} (w : (simple_graph_reconfiguration_graph G K).Walk a b)
    (v : V) : Finset ℕ :=
  (Finset.range w.length).filter (fun k => w.getVert k v ≠ w.getVert (k + 1) v)

theorem steps_unique {a b : G.Coloring (Fin K)}
    (w : (simple_graph_reconfiguration_graph G K).Walk a b) {u v : V} {s : ℕ}
    (hu : s ∈ steps w u) (hv : s ∈ steps w v) : u = v := by
  simp only [steps, Finset.mem_filter, Finset.mem_range] at hu hv
  obtain ⟨x, _, hx⟩ := w.adj_getVert_succ hu.1
  exact (hx u hu.2).trans (hx v hv.2).symm

theorem sum_steps_le {a b : G.Coloring (Fin K)}
    (w : (simple_graph_reconfiguration_graph G K).Walk a b) :
    ∑ v, (steps w v).card ≤ w.length := by
  rw [← Finset.card_biUnion]
  · calc _ ≤ (Finset.range w.length).card := by
          apply Finset.card_le_card
          intro s hs
          simp only [Finset.mem_biUnion] at hs
          obtain ⟨v, _, hv⟩ := hs
          simp only [steps, Finset.mem_filter] at hv
          exact hv.1
      _ = _ := Finset.card_range _
  · intro u _ v _ huv
    exact Finset.disjoint_left.mpr fun _ hu hv => huv (steps_unique w hu hv)

theorem getVert_const {a b : G.Coloring (Fin K)}
    (w : (simple_graph_reconfiguration_graph G K).Walk a b) (v : V) (k : ℕ) :
    ∀ k', k ≤ k' → (∀ s, k ≤ s → s < k' → s ∉ steps w v) →
      w.getVert k v = w.getVert k' v := by
  intro k' hk
  induction k', hk using Nat.le_induction with
  | base => intro _; rfl
  | succ n hn ih =>
    intro h
    rw [ih (fun s h1 h2 => h s h1 (by omega))]
    by_contra hne
    by_cases hL : n < w.length
    · exact h n hn (by omega) (by simp [steps, hL, hne])
    · apply hne
      rw [w.getVert_of_length_le (by omega), w.getVert_of_length_le (by omega)]

theorem steps_nonempty {a b : G.Coloring (Fin K)}
    (w : (simple_graph_reconfiguration_graph G K).Walk a b) {v : V} (h : a v ≠ b v) :
    1 ≤ (steps w v).card := by
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
  intro h0
  apply h
  have := getVert_const w v 0 w.length (Nat.zero_le _) (by simp [h0])
  simpa using this

theorem steps_one {a b : G.Coloring (Fin K)}
    (w : (simple_graph_reconfiguration_graph G K).Walk a b) {v : V} {s : ℕ}
    (h : steps w v = {s}) (k : ℕ) :
    w.getVert k v = if k ≤ s then a v else b v := by
  have hs : s < w.length := by
    have : s ∈ steps w v := by simp [h]
    simp only [steps, Finset.mem_filter, Finset.mem_range] at this; exact this.1
  split_ifs with hk
  · have := getVert_const w v 0 k (Nat.zero_le _) (by intro t _ ht; simp [h]; omega)
    simpa using this.symm
  · by_cases hkL : k ≤ w.length
    · have := getVert_const w v k w.length hkL (by intro t ht _; simp [h]; omega)
      simpa using this
    · rw [w.getVert_of_length_le (by omega)]

theorem steps_two {a b : G.Coloring (Fin K)}
    (w : (simple_graph_reconfiguration_graph G K).Walk a b) {v : V} {s₁ s₂ : ℕ}
    (h : steps w v = {s₁, s₂}) (h12 : s₁ < s₂) :
    ∃ m, m ≠ a v ∧ m ≠ b v ∧ ∀ k,
      w.getVert k v = if k ≤ s₁ then a v else if k ≤ s₂ then m else b v := by
  have hm1 : s₁ ∈ steps w v := by simp [h]
  have hm2 : s₂ ∈ steps w v := by simp [h]
  simp only [steps, Finset.mem_filter, Finset.mem_range] at hm1 hm2
  have e0 : ∀ k, k ≤ s₁ → w.getVert k v = a v := fun k hk => by
    have := getVert_const w v 0 k (Nat.zero_le _) (by intro t _ ht; simp [h]; omega)
    simpa using this.symm
  have e1 : ∀ k, s₁ < k → k ≤ s₂ → w.getVert k v = w.getVert (s₁ + 1) v := fun k hk1 hk2 => by
    have := getVert_const w v (s₁ + 1) k hk1 (by intro t ht1 ht2; simp [h]; omega)
    exact this.symm
  have e2 : ∀ k, s₂ < k → w.getVert k v = b v := fun k hk => by
    by_cases hkL : k ≤ w.length
    · have := getVert_const w v k w.length hkL (by intro t ht _; simp [h]; omega)
      simpa using this
    · rw [w.getVert_of_length_le (by omega)]
  refine ⟨w.getVert (s₁ + 1) v, ?_, ?_, ?_⟩
  · rw [← e0 s₁ le_rfl]; exact fun hh => hm1.2 hh.symm
  · rw [← e2 (s₂ + 1) (by omega), ← e1 s₂ h12 le_rfl]; exact hm2.2
  · intro k
    split_ifs with ha hb
    · exact e0 k ha
    · exact e1 k (by omega) hb
    · exact e2 k (by omega)


section claims

theorem α5_val (p : Fin 5 × Fin 5) :
    (α5 p).val = if p.1 = p.2 then p.1.val else 5 + p.1.val := rfl
theorem β5_val (p : Fin 5 × Fin 5) :
    (β5 p).val = if p.1 = p.2 then 5 + p.1.val else p.2.val := rfl

theorem adj_x_y {i j : Fin 5} (h : i ≠ j) : G5.Adj (i, i) (i, j) := Or.inl ⟨rfl, h, Or.inl rfl⟩
theorem adj_x_y' {i j : Fin 5} (h : j ≠ i) : G5.Adj (i, i) (j, i) := Or.inl ⟨rfl, h, Or.inr rfl⟩

variable (w : (simple_graph_reconfiguration_graph G5 10).Walk α5 β5)

theorem prop_at {p q : Fin 5 × Fin 5} (hadj : G5.Adj p q) (k : ℕ) :
    ((w.getVert k) p).val ≠ ((w.getVert k) q).val :=
  fun h => (w.getVert k).valid hadj (Fin.ext h)

theorem step_ne {p q : Fin 5 × Fin 5} (hpq : p ≠ q) {s t : ℕ} (hs : s ∈ steps w p)
    (ht : t ∈ steps w q) : s ≠ t := by
  rintro rfl; exact hpq (steps_unique w hs ht)

theorem claim2 {i j : Fin 5} (hij : i ≠ j) {s₁ s₂ t₁ t₂ : ℕ}
    (h1 : steps w (i, i) = {s₁}) (h2 : steps w (j, j) = {s₂})
    (h3 : steps w (i, j) = {t₁}) (h4 : steps w (j, i) = {t₂}) : False := by
  have hji : j ≠ i := Ne.symm hij
  have hi : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have d1 : t₁ ≠ s₁ := step_ne w (p := (i, j)) (q := (i, i)) (by simp [hij, hji]) (by simp [h3]) (by simp [h1])
  have d2 : t₁ ≠ s₂ := step_ne w (p := (i, j)) (q := (j, j)) (by simp [hij, hji]) (by simp [h3]) (by simp [h2])
  have d3 : t₂ ≠ s₁ := step_ne w (p := (j, i)) (q := (i, i)) (by simp [hij, hji]) (by simp [h4]) (by simp [h1])
  have d4 : t₂ ≠ s₂ := step_ne w (p := (j, i)) (q := (j, j)) (by simp [hij, hji]) (by simp [h4]) (by simp [h2])
  have c1 := prop_at w (adj_x_y hij) t₁
  have c2 := prop_at w (adj_x_y' hij) (t₁ + 1)
  have c3 := prop_at w (adj_x_y hji) t₂
  have c4 := prop_at w (adj_x_y' hji) (t₂ + 1)
  rw [steps_one w h1, steps_one w h3] at c1
  rw [steps_one w h2, steps_one w h3] at c2
  rw [steps_one w h2, steps_one w h4] at c3
  rw [steps_one w h1, steps_one w h4] at c4
  simp only [apply_ite Fin.val, α5_val, β5_val, hij, hji, if_true, if_false] at c1 c2 c3 c4
  split_ifs at c1 c2 c3 c4 <;> omega

theorem claim1_aux {i : Fin 5} {s₁ s₂ : ℕ} (h : steps w (i, i) = {s₁, s₂}) (h12 : s₁ < s₂) :
    ∃ j, j ≠ i ∧ (2 ≤ (steps w (i, j)).card ∨ 2 ≤ (steps w (j, i)).card) := by
  obtain ⟨m, hm1, hm2, hf⟩ := steps_two w h h12
  have hm1' : m.val ≠ i.val := fun e => hm1 (Fin.ext (by simp [α5_val, e]))
  have hm2' : m.val ≠ 5 + i.val := fun e => hm2 (Fin.ext (by simp [β5_val, e]))
  have hs1 : s₁ ∈ steps w (i, i) := by simp [h]
  have hs2 : s₂ ∈ steps w (i, i) := by simp [h]
  by_cases hm : m.val < 5
  · set j : Fin 5 := ⟨m.val, hm⟩ with hjdef
    have hij : i ≠ j := fun e => hm1' (by rw [e])
    refine ⟨j, Ne.symm hij, Or.inl ?_⟩
    by_contra hlt
    have hge := steps_nonempty w (α5_ne_β5 (i, j))
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp (by omega : (steps w (i, j)).card = 1)
    have htm : t ∈ steps w (i, j) := by simp [ht]
    have d1 := step_ne w (p := (i, j)) (q := (i, i)) (by simp [hij, Ne.symm hij]) htm hs1
    have d2 := step_ne w (p := (i, j)) (q := (i, i)) (by simp [hij, Ne.symm hij]) htm hs2
    have c1 := prop_at w (adj_x_y hij) (s₁ + 1)
    have c2 := prop_at w (adj_x_y hij) (t + 1)
    have c3 := prop_at w (adj_x_y hij) (s₂ + 1)
    rw [hf, steps_one w ht] at c1 c2 c3
    simp only [apply_ite Fin.val, α5_val, β5_val, hij, if_true, if_false, hjdef] at c1 c2 c3
    split_ifs at c1 c2 c3 <;> omega
  · set j : Fin 5 := ⟨m.val - 5, by omega⟩ with hjdef
    have hji : j ≠ i := fun e => hm2' (by rw [← e]; simp [hjdef]; omega)
    refine ⟨j, hji, Or.inr ?_⟩
    by_contra hlt
    have hge := steps_nonempty w (α5_ne_β5 (j, i))
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp (by omega : (steps w (j, i)).card = 1)
    have htm : t ∈ steps w (j, i) := by simp [ht]
    have d1 := step_ne w (p := (j, i)) (q := (i, i)) (by simp [hji, Ne.symm hji]) htm hs1
    have c1 := prop_at w (adj_x_y' hji) (s₁ + 1)
    have c2 := prop_at w (adj_x_y' hji) (t + 1)
    rw [hf, steps_one w ht] at c1 c2
    simp only [apply_ite Fin.val, α5_val, β5_val, hji, if_true, if_false, hjdef] at c1 c2
    split_ifs at c1 c2 <;> omega

theorem claim1 {i : Fin 5} (h : (steps w (i, i)).card = 2) :
    ∃ j, j ≠ i ∧ (2 ≤ (steps w (i, j)).card ∨ 2 ≤ (steps w (j, i)).card) := by
  obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.mp h
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact claim1_aux w he hlt
  · exact claim1_aux w (he.trans (Finset.pair_comm x y)) hlt

end claims


def bonusF (f : Fin 5 → Bool) (i : Fin 5) : ℕ :=
  if f i then ((Finset.univ.erase i).filter (fun j => f j = true)).card else 3

theorem bonus_sum : ∀ f : Fin 5 → Bool, 11 ≤ ∑ i, bonusF f i := by decide

theorem count_key (n : Fin 5 × Fin 5 → ℕ) (h1 : ∀ p, 1 ≤ n p)
    (hA : ∀ i j, i ≠ j → n (i, i) = 1 → n (j, j) = 1 → 2 ≤ n (i, j) ∨ 2 ≤ n (j, i))
    (hB : ∀ i, n (i, i) = 2 → ∃ j, j ≠ i ∧ (2 ≤ n (i, j) ∨ 2 ≤ n (j, i))) (i : Fin 5) :
    10 + bonusF (fun j => decide (n (j, j) = 1)) i ≤ ∑ j, (n (i, j) + n (j, i)) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hc : (Finset.univ.erase i).card = 4 := by simp
  have base : ∀ j ∈ Finset.univ.erase i, 2 ≤ n (i, j) + n (j, i) := fun j _ => by
    have := h1 (i, j); have := h1 (j, i); omega
  unfold bonusF
  by_cases hi1 : n (i, i) = 1
  · simp only [hi1, decide_true, if_true]
    have : ∑ j ∈ Finset.univ.erase i, (2 + if n (j, j) = 1 then 1 else 0) ≤
        ∑ j ∈ Finset.univ.erase i, (n (i, j) + n (j, i)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := base j hj
      have := h1 (i, j); have := h1 (j, i)
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      split_ifs with hj1
      · rcases hA i j (Ne.symm hji) hi1 hj1 with h | h <;> omega
      · omega
    rw [Finset.sum_add_distrib, Finset.sum_const, hc, Finset.sum_boole] at this
    simp only [smul_eq_mul, Nat.cast_id] at this
    have e : ((Finset.univ.erase i).filter (fun j => decide (n (j, j) = 1) = true)) =
        ((Finset.univ.erase i).filter (fun j => n (j, j) = 1)) := by
      ext j; simp
    rw [e]; omega
  · have hd : decide (n (i, i) = 1) = false := by simp [hi1]
    simp only [hd, if_false, Bool.false_eq_true]
    have hii := h1 (i, i)
    by_cases hi2 : n (i, i) = 2
    · obtain ⟨j0, hj0, hj0'⟩ := hB i hi2
      have : ∑ j ∈ Finset.univ.erase i, (2 + if j = j0 then 1 else 0) ≤
          ∑ j ∈ Finset.univ.erase i, (n (i, j) + n (j, i)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hb := base j hj
        have := h1 (i, j); have := h1 (j, i)
        split_ifs with hj1
        · subst hj1; rcases hj0' with h | h <;> omega
        · omega
      rw [Finset.sum_add_distrib, Finset.sum_const, hc,
        Finset.sum_ite_eq' (Finset.univ.erase i) j0 (fun _ => 1)] at this
      simp only [Finset.mem_erase, ne_eq, hj0, not_false_eq_true, Finset.mem_univ, and_self,
        if_true, smul_eq_mul] at this
      omega
    · have : ∑ j ∈ Finset.univ.erase i, 2 ≤ ∑ j ∈ Finset.univ.erase i, (n (i, j) + n (j, i)) :=
        Finset.sum_le_sum base
      rw [Finset.sum_const, hc, smul_eq_mul] at this
      omega

theorem count (n : Fin 5 × Fin 5 → ℕ) (h1 : ∀ p, 1 ≤ n p)
    (hA : ∀ i j, i ≠ j → n (i, i) = 1 → n (j, j) = 1 → 2 ≤ n (i, j) ∨ 2 ≤ n (j, i))
    (hB : ∀ i, n (i, i) = 2 → ∃ j, j ≠ i ∧ (2 ≤ n (i, j) ∨ 2 ≤ n (j, i))) :
    31 ≤ ∑ p, n p := by
  have e1 : ∑ p, n p = ∑ i, ∑ j, n (i, j) := Fintype.sum_prod_type _
  have e2 : ∑ i, ∑ j, n (j, i) = ∑ i, ∑ j, n (i, j) := Finset.sum_comm
  have hsum : ∑ i, (10 + bonusF (fun j => decide (n (j, j) = 1)) i) ≤
      ∑ i, ∑ j, (n (i, j) + n (j, i)) :=
    Finset.sum_le_sum fun i _ => count_key n h1 hA hB i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  have hb := bonus_sum (fun j => decide (n (j, j) = 1))
  omega

section conn
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {K : ℕ}

theorem reach_update (c : G.Coloring (Fin K)) (u : V) (col : Fin K)
    (hv : ∀ x, G.Adj u x → c x ≠ col) :
    ∃ c' : G.Coloring (Fin K), (∀ x, c' x = Function.update c u col x) ∧
      (simple_graph_reconfiguration_graph G K).Reachable c c' := by
  let c' : G.Coloring (Fin K) := SimpleGraph.Coloring.mk (Function.update c u col) (by
    intro a b hab
    by_cases ha : a = u
    · subst ha
      have hb : b ≠ a := (G.ne_of_adj hab).symm
      simp only [Function.update_self, Function.update_of_ne hb]
      exact (hv b hab).symm
    · by_cases hb : b = u
      · subst hb
        simp only [Function.update_self, Function.update_of_ne ha]
        exact hv a hab.symm
      · simp only [Function.update_of_ne ha, Function.update_of_ne hb]
        exact c.valid hab)
  refine ⟨c', fun x => rfl, ?_⟩
  by_cases hc : c u = col
  · have : c = c' := by
      refine RelHom.ext fun x => ?_
      show c x = Function.update c u col x
      by_cases hx : x = u
      · subst hx; simp [hc]
      · simp [Function.update_of_ne hx]
    rw [this]
  · apply SimpleGraph.Adj.reachable
    refine ⟨u, ?_, ?_⟩
    · show c u ≠ Function.update c u col u
      simpa using hc
    · intro y hy
      by_contra hyu
      apply hy
      show c y = Function.update c u col y
      simp [Function.update_of_ne hyu]

theorem exists_free_colour (hk : G.maxDegree + 2 ≤ K) (c : G.Coloring (Fin K)) (u : V)
    (b : Fin K) : ∃ col : Fin K, col ≠ b ∧ ∀ x, G.Adj u x → c x ≠ col := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin K)) ⊆
      insert b ((G.neighborFinset u).image (fun x => c x)) := by
    intro col _
    by_cases hb : col = b
    · simp [hb]
    · obtain ⟨x, hx, hcx⟩ := hcon col hb
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, by simpa using hx, hcx⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le b ((G.neighborFinset u).image (fun x => c x))
  have h3 := Finset.card_image_le (s := G.neighborFinset u) (f := fun x => c x)
  have h4 : (G.neighborFinset u).card ≤ G.maxDegree := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact G.degree_le_maxDegree u
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem clear_nbrs (hk : G.maxDegree + 2 ≤ K) (β : G.Coloring (Fin K)) (v : V) (t : Finset V) :
    ∀ m (c : G.Coloring (Fin K)),
      ((G.neighborFinset v).filter (fun u => c u = β v)).card ≤ m →
      (∀ w, w ∉ insert v t → c w = β w) →
      ∃ c1 : G.Coloring (Fin K), (simple_graph_reconfiguration_graph G K).Reachable c c1 ∧
        (∀ w, w ∉ insert v t → c1 w = β w) ∧ (∀ u, G.Adj v u → c1 u ≠ β v) := by
  intro m
  induction m with
  | zero =>
    intro c hm hc
    refine ⟨c, SimpleGraph.Reachable.refl _, hc, fun u hu hcu => ?_⟩
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hm
    exact hm (by simpa using hu) hcu
  | succ m ih =>
    intro c hm hc
    by_cases hle : ((G.neighborFinset v).filter (fun u => c u = β v)).card ≤ m
    · exact ih c hle hc
    obtain ⟨u, hu⟩ : ((G.neighborFinset v).filter (fun u => c u = β v)).Nonempty := by
      rw [← Finset.card_pos]; omega
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu
    have hut : u ∈ insert v t := by
      by_contra hnot
      have := hc u hnot
      exact β.valid hu.1 (hu.2.symm.trans this)
    obtain ⟨col, hcolb, hcol⟩ := exists_free_colour hk c u (β v)
    obtain ⟨c', hc'eq, hreach⟩ := reach_update c u col hcol
    have hsub : (G.neighborFinset v).filter (fun x => c' x = β v) ⊆
        ((G.neighborFinset v).filter (fun x => c x = β v)).erase u := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_erase] at hx ⊢
      rw [hc'eq] at hx
      by_cases hxu : x = u
      · subst hxu; simp at hx; exact absurd hx.2 hcolb
      · simp only [Function.update_of_ne hxu] at hx
        exact ⟨hxu, hx⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp [hu.1, hu.2])] at hcard
    have hc' : ∀ w, w ∉ insert v t → c' w = β w := by
      intro w hw
      rw [hc'eq]
      have hwu : w ≠ u := fun h => hw (h ▸ hut)
      simp only [Function.update_of_ne hwu]; exact hc w hw
    obtain ⟨c1, h1, h2, h3⟩ := ih c' (by omega) hc'
    exact ⟨c1, hreach.trans h1, h2, h3⟩

theorem reach_beta (hk : G.maxDegree + 2 ≤ K) (β : G.Coloring (Fin K)) (s : Finset V) :
    ∀ c : G.Coloring (Fin K), (∀ w, w ∉ s → c w = β w) →
      (simple_graph_reconfiguration_graph G K).Reachable c β := by
  induction s using Finset.induction_on with
  | empty =>
    intro c hc
    have : c = β := RelHom.ext fun x => hc x (Finset.notMem_empty x)
    rw [this]
  | insert v t hv ih =>
    intro c hc
    obtain ⟨c1, hr1, hc1, hnb⟩ := clear_nbrs hk β v t _ c le_rfl hc
    obtain ⟨c2, hc2eq, hr2⟩ := reach_update c1 v (β v) (fun x hx => hnb x hx)
    refine hr1.trans (hr2.trans (ih c2 fun w hw => ?_))
    rw [hc2eq]
    by_cases hwv : w = v
    · subst hwv; simp
    · simp only [Function.update_of_ne hwv]
      exact hc1 w (by simp [hwv, hw])

theorem recolour_connected (hk : G.maxDegree + 2 ≤ K) (a b : G.Coloring (Fin K)) :
    (simple_graph_reconfiguration_graph G K).Reachable a b :=
  reach_beta hk b Finset.univ a (fun w hw => absurd (Finset.mem_univ w) hw)

end conn

theorem walk_len (w : (simple_graph_reconfiguration_graph G5 10).Walk α5 β5) : 31 ≤ w.length := by
  have hA : ∀ i j : Fin 5, i ≠ j → (steps w (i, i)).card = 1 → (steps w (j, j)).card = 1 →
      2 ≤ (steps w (i, j)).card ∨ 2 ≤ (steps w (j, i)).card := by
    intro i j hij h1 h2
    by_contra hne
    push Not at hne
    have g3 := steps_nonempty w (α5_ne_β5 (i, j))
    have g4 := steps_nonempty w (α5_ne_β5 (j, i))
    obtain ⟨s₁, hs₁⟩ := Finset.card_eq_one.mp h1
    obtain ⟨s₂, hs₂⟩ := Finset.card_eq_one.mp h2
    obtain ⟨t₁, ht₁⟩ := Finset.card_eq_one.mp (by omega : (steps w (i, j)).card = 1)
    obtain ⟨t₂, ht₂⟩ := Finset.card_eq_one.mp (by omega : (steps w (j, i)).card = 1)
    exact claim2 w hij hs₁ hs₂ ht₁ ht₂
  have := count (fun p => (steps w p).card) (fun p => steps_nonempty w (α5_ne_β5 p)) hA
    (fun i h => claim1 w h)
  exact this.trans (sum_steps_le w)

theorem le_eight_aux : simple_graph_reconfiguration_diam_gt_matching 8 := by
  refine ⟨Fin 5 × Fin 5, inferInstance, inferInstance, G5, inferInstance, G5_maxDegree, ?_⟩
  have : Nonempty (G5.Coloring (Fin 10)) := ⟨α5⟩
  have : Finite (G5.Coloring (Fin 10)) := Finite.of_injective _ DFunLike.coe_injective
  have hconn : (simple_graph_reconfiguration_graph G5 (8 + 2)).Connected :=
    ⟨fun a b => recolour_connected (by rw [G5_maxDegree]) a b⟩
  have hne := SimpleGraph.connected_iff_ediam_ne_top.mp hconn
  obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist α5 β5
  have h31 : 31 ≤ (simple_graph_reconfiguration_graph G5 (8 + 2)).diam :=
    ((walk_len w).trans hw.le).trans (SimpleGraph.dist_le_diam hne)
  have hcard : Fintype.card (Fin 5 × Fin 5) = 25 := by simp
  rw [hcard]
  calc ((25 : ℕ) : ℕ∞) + graph_matching_num G5 ≤ 25 + 5 := add_le_add le_rfl G5_matching
    _ < 31 := by norm_num
    _ ≤ _ := by exact_mod_cast h31

end Op1611LeEight

/-- Theorem 4 of arXiv:2611.17022: an 8-regular graph certifying that the minimal maximum degree is at most 8. -/
theorem op_1611_min_max_degree_le_eight :
    simple_graph_reconfiguration_diam_gt_matching 8 := by
  exact Op1611LeEight.le_eight_aux
