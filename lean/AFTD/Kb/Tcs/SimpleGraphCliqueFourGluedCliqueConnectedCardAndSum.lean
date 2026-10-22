import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCliqueFourGluedClique
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# simple_graph_clique_four_glued_clique_connected_card_and_sum

Topic: graphs   Node: f5e4c1f2437f

Provenance: helper lemma. step towards simple_graph_avg_connected_induced_order_clique_four_glued_clique

For n ≥ 7, the number of subsets of Fin n that induce a connected subgraph in simple_graph_clique_four_glued_clique n is 2^(n-4) + 2^(n-1) + 6, and the sum of their cardinalities is 12 + (n-4)*2^(n-5) + 2^(n-1) + (n-1)*2^(n-2).
-/

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_adj (n : ℕ) (i j : Fin n) :
    (simple_graph_clique_four_glued_clique n).Adj i j ↔
      i ≠ j ∧ ((i.val ≤ 3 ∧ j.val ≤ 3) ∨ (3 ≤ i.val ∧ 3 ≤ j.val)) := Iff.rfl

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_reachable_mem_of_closed
    {V : Type*} {G : SimpleGraph V} {T : Set V}
    (hT : ∀ v ∈ T, ∀ w, G.Adj v w → w ∈ T) {u v : V} (hu : u ∈ T) (h : G.Reachable u v) : v ∈ T := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hT _ hu _ hadj)

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_connected_of_center
    (n : ℕ) {S : Finset (Fin n)} {c : Fin n} (hc : c.val = 3) (hm : c ∈ S) :
    ((simple_graph_clique_four_glued_clique n).induce (S : Set (Fin n))).Connected := by
  classical
  have hstar : ∀ x : ↥(S : Set (Fin n)),
      ((simple_graph_clique_four_glued_clique n).induce (S : Set (Fin n))).Adj x ⟨c, hm⟩ ∨ x = ⟨c, hm⟩ := by
    intro x
    by_cases hx : x = ⟨c, hm⟩
    · exact Or.inr hx
    · left
      rw [SimpleGraph.induce_adj, simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_adj]
      refine ⟨fun h => hx (Subtype.ext h), ?_⟩
      rcases Nat.le_or_le x.1.val 3 with h | h
      · exact Or.inl ⟨h, by simpa using hc.le⟩
      · exact Or.inr ⟨h, by simpa using hc.ge⟩
  haveI : Nonempty ↥(S : Set (Fin n)) := ⟨⟨c, hm⟩⟩
  refine SimpleGraph.Connected.mk (fun x y => ?_)
  have hx : ((simple_graph_clique_four_glued_clique n).induce (S : Set (Fin n))).Reachable x ⟨c, hm⟩ :=
    (hstar x).elim (fun h => h.reachable) (fun h => h ▸ SimpleGraph.Reachable.refl _)
  have hy : ((simple_graph_clique_four_glued_clique n).induce (S : Set (Fin n))).Reachable y ⟨c, hm⟩ :=
    (hstar y).elim (fun h => h.reachable) (fun h => h ▸ SimpleGraph.Reachable.refl _)
  exact hx.trans hy.symm

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_connected_of_forall_le_three
    (n : ℕ) (S : Finset (Fin n)) (hne : S.Nonempty) (h : ∀ x ∈ S, x.val ≤ 3) :
    ((simple_graph_clique_four_glued_clique n).induce (S : Set (Fin n))).Connected := by
  classical
  haveI : Nonempty ↥(S : Set (Fin n)) := hne.to_subtype
  refine SimpleGraph.Connected.mk (fun x y => ?_)
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.induce_adj, simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_adj]
    exact ⟨fun hc => hxy (Subtype.ext hc), Or.inl ⟨h x.1 x.2, h y.1 y.2⟩⟩

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_connected_of_forall_three_le
    (n : ℕ) (S : Finset (Fin n)) (hne : S.Nonempty) (h : ∀ x ∈ S, 3 ≤ x.val) :
    ((simple_graph_clique_four_glued_clique n).induce (S : Set (Fin n))).Connected := by
  classical
  haveI : Nonempty ↥(S : Set (Fin n)) := hne.to_subtype
  refine SimpleGraph.Connected.mk (fun x y => ?_)
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.induce_adj, simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_adj]
    exact ⟨fun hc => hxy (Subtype.ext hc), Or.inr ⟨h x.1 x.2, h y.1 y.2⟩⟩

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_conn_iff
    (n : ℕ) (S : Finset (Fin n)) :
    ((simple_graph_clique_four_glued_clique n).induce (S : Set (Fin n))).Connected ↔
      (∃ x ∈ S, x.val = 3) ∨ (S.Nonempty ∧ ∀ x ∈ S, x.val ≤ 2) ∨
        (S.Nonempty ∧ ∀ x ∈ S, 4 ≤ x.val) := by
  classical
  constructor
  · intro hc
    by_cases h3 : ∃ x ∈ S, x.val = 3
    · exact Or.inl h3
    · push Not at h3
      right
      obtain ⟨⟨x, hxS⟩⟩ := hc.nonempty
      rcases Nat.lt_or_ge x.val 3 with hx | hx
      · left
        refine ⟨⟨x, hxS⟩, fun y hy => ?_⟩
        have hr :
          ((simple_graph_clique_four_glued_clique n).induce (S : Set (Fin n))).Reachable
            ⟨x, hxS⟩ ⟨y, hy⟩ := hc.preconnected _ _
        exact simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_reachable_mem_of_closed
          (T := {z : ↥(S : Set (Fin n)) | z.1.val ≤ 2})
          (fun v hv w hw => by
            simp only [Set.mem_ofPred_eq] at hv ⊢
            rw [SimpleGraph.induce_adj,
              simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_adj] at hw
            have hw3 : w.1.val ≠ 3 := h3 w.1 w.2
            omega)
          (show (⟨x, hxS⟩ : ↥(S : Set (Fin n))) ∈ {z | z.1.val ≤ 2} from by
            show x.val ≤ 2
            omega)
          hr
      · right
        refine ⟨⟨x, hxS⟩, fun y hy => ?_⟩
        have hr :
          ((simple_graph_clique_four_glued_clique n).induce (S : Set (Fin n))).Reachable
            ⟨x, hxS⟩ ⟨y, hy⟩ := hc.preconnected _ _
        exact simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_reachable_mem_of_closed
          (T := {z : ↥(S : Set (Fin n)) | 4 ≤ z.1.val})
          (fun v hv w hw => by
            simp only [Set.mem_ofPred_eq] at hv ⊢
            rw [SimpleGraph.induce_adj,
              simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_adj] at hw
            have hw3 : w.1.val ≠ 3 := h3 w.1 w.2
            omega)
          (show (⟨x, hxS⟩ : ↥(S : Set (Fin n))) ∈ {z | 4 ≤ z.1.val} from by
            show 4 ≤ x.val
            have := h3 x hxS
            omega)
          hr
  · rintro (⟨x, hxS, hx3⟩ | ⟨hne, h2⟩ | ⟨hne, h4⟩)
    · exact simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_connected_of_center n hx3 hxS
    · exact simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_connected_of_forall_le_three
        n S hne (fun x hx => by have := h2 x hx; omega)
    · exact simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_connected_of_forall_three_le
        n S hne (fun x hx => by have := h4 x hx; omega)

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_two_mul_pow_pred (k : ℕ) :
    2 * (k * 2 ^ (k - 1)) + 2 ^ k = (k + 1) * 2 ^ k := by
  match k with
  | 0 => simp
  | (j + 1) =>
    have hk1 : 2 ^ (j + 1 - 1) = 2 ^ j := by simp
    have hk2 : 2 ^ (j + 1) = 2 ^ j * 2 := by rw [pow_succ]
    rw [hk1, hk2]
    ring

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_powerset
    {α : Type*} (s : Finset α) :
    ∑ t ∈ s.powerset, t.card = s.card * 2 ^ (s.card - 1) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have h2 : ∑ t ∈ s.powerset, (insert a t).card = ∑ t ∈ s.powerset, (t.card + 1) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [Finset.card_insert_of_notMem]
      intro h
      exact ha (Finset.mem_powerset.mp ht h)
    rw [h2, Finset.sum_add_distrib, ih, Finset.sum_const, Finset.card_powerset,
      Finset.card_insert_of_notMem ha]
    simp only [smul_eq_mul, mul_one]
    have hk : s.card + 1 - 1 = s.card := by omega
    rw [hk]
    have h := simple_graph_clique_four_glued_clique_connected_card_and_sum_two_mul_pow_pred s.card
    omega

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_card_nonempty_powerset
    {α : Type*} (s : Finset α) :
    (s.powerset.filter Finset.Nonempty).card = 2 ^ s.card - 1 := by
  classical
  have h : s.powerset.filter Finset.Nonempty = s.powerset.erase ∅ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.nonempty_iff_ne_empty]
    tauto
  rw [h, Finset.card_erase_of_mem (Finset.empty_mem_powerset s), Finset.card_powerset]

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_nonempty_powerset
    {α : Type*} (s : Finset α) :
    ∑ t ∈ s.powerset.filter Finset.Nonempty, t.card = s.card * 2 ^ (s.card - 1) := by
  classical
  rw [← simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_powerset s]
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro x hx hx'
  have hxe : x = ∅ := by
    by_contra h
    exact hx' (Finset.mem_filter.mpr ⟨hx, Finset.nonempty_iff_ne_empty.mpr h⟩)
  rw [hxe]
  simp

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_insert_injOn_powerset_erase
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    Set.InjOn (fun t : Finset α => insert a t) ((Finset.univ.erase a).powerset : Set (Finset α)) := by
  intro t1 ht1 t2 ht2 h
  simp only [Finset.mem_coe, Finset.mem_powerset] at ht1 ht2
  have h1 : a ∉ t1 := fun hh => (Finset.mem_erase.mp (ht1 hh)).1 rfl
  have h2 : a ∉ t2 := fun hh => (Finset.mem_erase.mp (ht2 hh)).1 rfl
  have hh := congrArg (fun s => s.erase a) h
  rwa [Finset.erase_insert h1, Finset.erase_insert h2] at hh

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_filter_mem_univ_eq_image
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    (Finset.univ.filter (fun S : Finset α => a ∈ S))
      = (Finset.univ.erase a).powerset.image (insert a) := by
  ext S
  constructor
  · intro h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    refine Finset.mem_image.mpr ⟨S.erase a, ?_, Finset.insert_erase h⟩
    refine Finset.mem_powerset.mpr (fun y hy => ?_)
    rw [Finset.mem_erase]
    exact ⟨(Finset.mem_erase.mp hy).1, Finset.mem_univ y⟩
  · intro h
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self a t⟩

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_card_filter_mem_univ
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    (Finset.univ.filter (fun S : Finset α => a ∈ S)).card = 2 ^ (Fintype.card α - 1) := by
  classical
  rw [simple_graph_clique_four_glued_clique_connected_card_and_sum_filter_mem_univ_eq_image,
    Finset.card_image_of_injOn
      (simple_graph_clique_four_glued_clique_connected_card_and_sum_insert_injOn_powerset_erase a),
    Finset.card_powerset, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_filter_mem_univ
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset α => a ∈ S), S.card
      = (Fintype.card α - 1) * 2 ^ (Fintype.card α - 2) + 2 ^ (Fintype.card α - 1) := by
  classical
  rw [simple_graph_clique_four_glued_clique_connected_card_and_sum_filter_mem_univ_eq_image,
    Finset.sum_image
      (simple_graph_clique_four_glued_clique_connected_card_and_sum_insert_injOn_powerset_erase a)]
  have h2 : ∑ t ∈ (Finset.univ.erase a).powerset, (insert a t).card
      = ∑ t ∈ (Finset.univ.erase a).powerset, (t.card + 1) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [Finset.card_insert_of_notMem]
    intro hh
    exact (Finset.mem_erase.mp (Finset.mem_powerset.mp ht hh)).1 rfl
  rw [h2, Finset.sum_add_distrib,
    simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_powerset,
    Finset.sum_const, Finset.card_powerset,
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
  simp only [smul_eq_mul, mul_one]
  rw [Nat.sub_sub]

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_card_filter_val_le_two
    (n : ℕ) (hn : 4 ≤ n) :
    (Finset.univ.filter (fun x : Fin n => x.val ≤ 2)).card = 3 := by
  classical
  have h : (Finset.univ.filter (fun x : Fin n => x.val ≤ 2)).card
      = (Finset.univ : Finset (Fin 3)).card := by
    refine Finset.card_bij (fun x hx => (⟨x.val, ?_⟩ : Fin 3)) ?_ ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      omega
    · intro a ha
      exact Finset.mem_univ _
    · intro a1 ha1 a2 ha2 heq
      have hh := congrArg (fun t : Fin 3 => t.val) heq
      simp only at hh
      exact Fin.ext hh
    · intro b hb
      refine ⟨⟨b.val, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · exact Fin.ext rfl
  rw [h, Finset.card_univ, Fintype.card_fin]

lemma simple_graph_clique_four_glued_clique_connected_card_and_sum_card_filter_val_ge_four
    (n : ℕ) (hn : 7 ≤ n) :
    (Finset.univ.filter (fun x : Fin n => 4 ≤ x.val)).card = n - 4 := by
  classical
  have h : (Finset.univ.filter (fun x : Fin n => 4 ≤ x.val)).card
      = (Finset.univ : Finset (Fin (n - 4))).card := by
    refine Finset.card_bij (fun x hx => (⟨x.val - 4, ?_⟩ : Fin (n - 4))) ?_ ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      omega
    · intro a ha
      exact Finset.mem_univ _
    · intro a1 ha1 a2 ha2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha1 ha2
      have hh := congrArg (fun t : Fin (n - 4) => t.val) heq
      simp only at hh
      omega
    · intro b hb
      refine ⟨⟨b.val + 4, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · exact Fin.ext (by simp)
  rw [h, Finset.card_univ, Fintype.card_fin]

/-- The number of connected induced subsets and the sum of their cardinalities in K_4 glued to K_{n-3} at a vertex. -/
theorem simple_graph_clique_four_glued_clique_connected_card_and_sum (n : ℕ) (hn : 7 ≤ n) :
    let G := simple_graph_clique_four_glued_clique n
    haveI : DecidableRel G.Adj := Classical.decRel _
    haveI : ∀ S : Finset (Fin n), Decidable (G.induce (S : Set (Fin n))).Connected := fun _ => Classical.dec _
    (Finset.univ.filter (fun S : Finset (Fin n) => (G.induce (S : Set (Fin n))).Connected)).card =
      2 ^ (n - 4) + 2 ^ (n - 1) + 6 ∧
    (Finset.univ.filter (fun S : Finset (Fin n) => (G.induce (S : Set (Fin n))).Connected)).sum Finset.card =
      12 + (n - 4) * 2 ^ (n - 5) + 2 ^ (n - 1) + (n - 1) * 2 ^ (n - 2) := by
  classical
  dsimp only
  rw [Finset.filter_congr_decidable (s := Finset.univ)
    (p := fun S : Finset (Fin n) => (SimpleGraph.induce (↑S) (simple_graph_clique_four_glued_clique n)).Connected)
    (Classical.decPred _)]
  set v3 : Fin n := ⟨3, by omega⟩ with hv3
  have hv3val : v3.val = 3 := rfl
  set A : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => x.val ≤ 2) with hA
  set C : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => 4 ≤ x.val) with hC
  set F1 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S : Finset (Fin n) => ∃ x ∈ S, x.val = 3) with hF1
  set F2 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S : Finset (Fin n) => S.Nonempty ∧ ∀ x ∈ S, x.val ≤ 2) with hF2
  set F3 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S : Finset (Fin n) => S.Nonempty ∧ ∀ x ∈ S, 4 ≤ x.val) with hF3
  have hT : (Finset.univ.filter (fun S : Finset (Fin n) => (SimpleGraph.induce (↑S) (simple_graph_clique_four_glued_clique n)).Connected))
      = F1 ∪ (F2 ∪ F3) := by
    rw [hF1, hF2, hF3, ← Finset.filter_or, ← Finset.filter_or]
    exact Finset.filter_congr (fun S _ => simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_conn_iff n S)
  have hd23 : Disjoint F2 F3 := by
    rw [hF2, hF3]
    refine Finset.disjoint_left.mpr ?_
    intro S hS hS'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS hS'
    obtain ⟨x, hx⟩ := hS.1
    have h2 := hS.2 x hx
    have h4 := hS'.2 x hx
    omega
  have hd1 : Disjoint F1 (F2 ∪ F3) := by
    rw [hF1, hF2, hF3]
    refine Finset.disjoint_left.mpr ?_
    intro S hS hS'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [Finset.mem_union] at hS'
    obtain ⟨x, hxS, hx3⟩ := hS
    rcases hS' with hS' | hS'
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS'
      have := hS'.2 x hxS
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS'
      have := hS'.2 x hxS
      omega
  have hF1eq : F1 = Finset.univ.filter (fun S : Finset (Fin n) => v3 ∈ S) := by
    rw [hF1]
    refine Finset.filter_congr (fun S _ => ?_)
    constructor
    · rintro ⟨x, hxS, hx3⟩
      have hx : x = v3 := Fin.ext (by rw [hv3val]; exact hx3)
      rwa [hx] at hxS
    · rintro h
      exact ⟨v3, h, hv3val⟩
  have hF1card : F1.card = 2 ^ (n - 1) := by
    rw [hF1eq, simple_graph_clique_four_glued_clique_connected_card_and_sum_card_filter_mem_univ v3,
      Fintype.card_fin]
  have hF1sum : ∑ S ∈ F1, S.card = (n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1) := by
    rw [hF1eq, simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_filter_mem_univ v3,
      Fintype.card_fin]
  have hAcard : A.card = 3 := by
    rw [hA]; exact simple_graph_clique_four_glued_clique_connected_card_and_sum_card_filter_val_le_two n (by omega)
  have hCcard : C.card = n - 4 := by
    rw [hC]; exact simple_graph_clique_four_glued_clique_connected_card_and_sum_card_filter_val_ge_four n hn
  have hF2eq : F2 = A.powerset.filter Finset.Nonempty := by
    rw [hF2, hA]
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset, Finset.subset_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hF3eq : F3 = C.powerset.filter Finset.Nonempty := by
    rw [hF3, hC]
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset, Finset.subset_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hF2card : F2.card = 7 := by
    rw [hF2eq, simple_graph_clique_four_glued_clique_connected_card_and_sum_card_nonempty_powerset,
      hAcard]; norm_num
  have hF2sum : ∑ S ∈ F2, S.card = 12 := by
    rw [hF2eq, simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_nonempty_powerset,
      hAcard]; norm_num
  have hF3card : F3.card = 2 ^ (n - 4) - 1 := by
    rw [hF3eq, simple_graph_clique_four_glued_clique_connected_card_and_sum_card_nonempty_powerset, hCcard]
  have hF3sum : ∑ S ∈ F3, S.card = (n - 4) * 2 ^ (n - 5) := by
    rw [hF3eq, simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_nonempty_powerset,
      hCcard]
    rw [show n - 4 - 1 = n - 5 by omega]
  constructor
  · rw [hT]
    rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd23,
      hF1card, hF2card, hF3card]
    have hp : 1 ≤ 2 ^ (n - 4) := Nat.one_le_two_pow
    omega
  · rw [hT]
    rw [Finset.sum_union hd1, Finset.sum_union hd23, hF1sum, hF2sum, hF3sum]
    ring
