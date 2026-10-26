import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCliqueFourBridgeClique
import AFTD.Kb.Tcs.SimpleGraphCliqueFourGluedCliqueConnectedCardAndSum
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# simple_graph_clique_four_bridge_clique_connected_card_and_sum

Topic: graphs   Node: 7c0db89f966c

Provenance: helper lemma. step towards simple_graph_avg_connected_induced_order_clique_four_bridge_clique

For n ≥ 8, the number of subsets of Fin n that induce a connected subgraph in simple_graph_clique_four_bridge_clique n is 5 * 2^(n-4) + 14, and the sum of their cardinalities is 32 + (n+24)*2^(n-5) + (n-5)*2^(n-3).
-/

private lemma in148_card_filter_val_le_three (n : ℕ) (hn : 4 ≤ n) :
    (Finset.univ.filter (fun x : Fin n => x.val ≤ 3)).card = 4 := by
  have h : (Finset.univ.filter (fun x : Fin n => x.val ≤ 3)) =
      Finset.image (fun i : Fin 4 => (⟨i.val, by omega⟩ : Fin n)) Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      use ⟨x.val, by omega⟩
    · rintro ⟨i, _, rfl⟩
      exact Nat.le_of_lt_succ i.isLt
  rw [h, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    have := congr_arg Fin.val hab
    exact Fin.ext this


private lemma in148_filter_pair_mem_univ_eq_image {α : Type*} [Fintype α] [DecidableEq α] (a b : α) (hab : a ≠ b) :
    (Finset.univ.filter (fun S : Finset α => a ∈ S ∧ b ∈ S)) =
      ((Finset.univ.erase a).erase b).powerset.image (fun t => insert a (insert b t)) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_powerset, Finset.subset_iff,
    Finset.mem_erase]
  constructor
  · intro ⟨ha, hb⟩
    refine ⟨(S.erase a).erase b, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
    · have hb' : b ∈ S.erase a := by
        rw [Finset.mem_erase]
        exact ⟨hab.symm, hb⟩
      rw [Finset.insert_erase hb', Finset.insert_erase ha]
  · rintro ⟨t, ht, rfl⟩
    simp only [Finset.mem_insert, true_or, or_true, and_self]


private lemma in148_insert_pair_injOn {α : Type*} [Fintype α] [DecidableEq α] (a b : α) (hab : a ≠ b) :
    Set.InjOn (fun t : Finset α => insert a (insert b t))
      (((Finset.univ.erase a).erase b).powerset : Set (Finset α)) := by
  intro t1 ht1 t2 ht2 heq
  change insert a (insert b t1) = insert a (insert b t2) at heq
  rw [Finset.mem_coe, Finset.mem_powerset] at ht1 ht2
  have hna1 : a ∉ insert b t1 := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab, fun ha => (Finset.mem_erase.mp (Finset.mem_erase.mp (ht1 ha)).2).1 rfl⟩
  have hna2 : a ∉ insert b t2 := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab, fun ha => (Finset.mem_erase.mp (Finset.mem_erase.mp (ht2 ha)).2).1 rfl⟩
  have h1 : (insert a (insert b t1)).erase a = insert b t1 := Finset.erase_insert hna1
  have h2 : (insert a (insert b t2)).erase a = insert b t2 := Finset.erase_insert hna2
  have h12 : insert b t1 = insert b t2 := by
    rw [← h1, ← h2, heq]
  have hnb1 : b ∉ t1 := fun hb => (Finset.mem_erase.mp (ht1 hb)).1 rfl
  have hnb2 : b ∉ t2 := fun hb => (Finset.mem_erase.mp (ht2 hb)).1 rfl
  rw [← Finset.erase_insert hnb1, ← Finset.erase_insert hnb2, h12]

private lemma in148_connected_iff (n : ℕ) (v3 v4 : Fin n) (hv3 : v3.val = 3) (hv4 : v4.val = 4)
    (S : Finset (Fin n)) :
    ((simple_graph_clique_four_bridge_clique n).induce (S : Set (Fin n))).Connected ↔
      (S.Nonempty ∧ ∀ x ∈ S, x.val ≤ 3) ∨
      (S.Nonempty ∧ ∀ x ∈ S, 4 ≤ x.val) ∨ (v3 ∈ S ∧ v4 ∈ S) := by
  classical
  let H := (simple_graph_clique_four_bridge_clique n).induce (S : Set (Fin n))
  constructor
  · intro hc
    by_cases hb : v3 ∈ S ∧ v4 ∈ S
    · exact Or.inr (Or.inr hb)
    have no_cross (v w : ↥(S : Set (Fin n))) (hv : v.1.val ≤ 3) (hw : 4 ≤ w.1.val)
        (hadj : H.Adj v w) : False := by
      change v.1 ≠ w.1 ∧ ((v.1.val ≤ 3 ∧ w.1.val ≤ 3) ∨
        (4 ≤ v.1.val ∧ 4 ≤ w.1.val) ∨ (v.1.val = 3 ∧ w.1.val = 4) ∨
        (v.1.val = 4 ∧ w.1.val = 3)) at hadj
      have he3 : v.1 = v3 := Fin.ext (by omega)
      have he4 : w.1 = v4 := Fin.ext (by omega)
      have hm3 : v3 ∈ S := he3 ▸ v.2
      have hm4 : v4 ∈ S := he4 ▸ w.2
      exact hb ⟨hm3,hm4⟩
    obtain ⟨⟨x,hxS⟩⟩ := hc.nonempty
    by_cases hx : x.val ≤ 3
    · left
      refine ⟨⟨x,hxS⟩,fun y hy => ?_⟩
      exact simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_reachable_mem_of_closed
        (G := H) (T := {z | z.1.val ≤ 3})
        (fun v hv w hadj => by
          change v.1.val ≤ 3 at hv
          change w.1.val ≤ 3
          by_contra hw
          exact no_cross v w hv (by omega) hadj)
        (u := ⟨x,hxS⟩) (by exact hx) (hc.preconnected _ ⟨y,hy⟩)
    · right; left
      refine ⟨⟨x,hxS⟩,fun y hy => ?_⟩
      exact simple_graph_clique_four_glued_clique_connected_card_and_sum_sgc_reachable_mem_of_closed
        (G := H) (T := {z | 4 ≤ z.1.val})
        (fun v hv w hadj => by
          change 4 ≤ v.1.val at hv
          change 4 ≤ w.1.val
          by_contra hw
          exact no_cross w v (by omega) hv hadj.symm)
        (u := ⟨x,hxS⟩) (by change 4 ≤ x.val; omega) (hc.preconnected _ ⟨y,hy⟩)
  · rintro (⟨hne,hleft⟩ | ⟨hne,hright⟩ | ⟨h3,h4⟩)
    · haveI : Nonempty ↥(S : Set (Fin n)) := hne.to_subtype
      refine SimpleGraph.Connected.mk (fun x y => ?_)
      by_cases hxy : x = y
      · subst y; exact SimpleGraph.Reachable.refl _
      · apply SimpleGraph.Adj.reachable
        change x.1 ≠ y.1 ∧ ((x.1.val ≤ 3 ∧ y.1.val ≤ 3) ∨ _)
        exact ⟨fun he => hxy (Subtype.ext he),Or.inl ⟨hleft x.1 x.2,hleft y.1 y.2⟩⟩
    · haveI : Nonempty ↥(S : Set (Fin n)) := hne.to_subtype
      refine SimpleGraph.Connected.mk (fun x y => ?_)
      by_cases hxy : x = y
      · subst y; exact SimpleGraph.Reachable.refl _
      · apply SimpleGraph.Adj.reachable
        change x.1 ≠ y.1 ∧ (_ ∨ (4 ≤ x.1.val ∧ 4 ≤ y.1.val) ∨ _)
        exact ⟨fun he => hxy (Subtype.ext he),Or.inr (Or.inl ⟨hright x.1 x.2,hright y.1 y.2⟩)⟩
    · haveI : Nonempty ↥(S : Set (Fin n)) := ⟨⟨v3,h3⟩⟩
      have hL (x : ↥(S : Set (Fin n))) (hx : x.1.val ≤ 3) : H.Reachable x ⟨v3,h3⟩ := by
        by_cases he : x = ⟨v3,h3⟩
        · rw [he]
        · apply SimpleGraph.Adj.reachable
          change x.1 ≠ v3 ∧ ((x.1.val ≤ 3 ∧ v3.val ≤ 3) ∨ _)
          exact ⟨fun hh => he (Subtype.ext hh),Or.inl ⟨hx,by omega⟩⟩
      have hR (x : ↥(S : Set (Fin n))) (hx : 4 ≤ x.1.val) : H.Reachable x ⟨v4,h4⟩ := by
        by_cases he : x = ⟨v4,h4⟩
        · rw [he]
        · apply SimpleGraph.Adj.reachable
          change x.1 ≠ v4 ∧ (_ ∨ (4 ≤ x.1.val ∧ 4 ≤ v4.val) ∨ _)
          exact ⟨fun hh => he (Subtype.ext hh),Or.inr (Or.inl ⟨hx,by omega⟩)⟩
      have hbridge : H.Reachable ⟨v4,h4⟩ ⟨v3,h3⟩ := by
        apply SimpleGraph.Adj.reachable
        change v4 ≠ v3 ∧ (_ ∨ _ ∨ _ ∨ (v4.val = 4 ∧ v3.val = 3))
        exact ⟨fun he => by have := congrArg Fin.val he; omega,Or.inr (Or.inr (Or.inr ⟨hv4,hv3⟩))⟩
      have hgo (x : ↥(S : Set (Fin n))) : H.Reachable x ⟨v3,h3⟩ := by
        by_cases hx : x.1.val ≤ 3
        · exact hL x hx
        · exact (hR x (by omega)).trans hbridge
      exact SimpleGraph.Connected.mk (fun x y => (hgo x).trans (hgo y).symm)

private lemma in148_pair_card_sum {α : Type*} [Fintype α] [DecidableEq α] (a b : α) (hab : a ≠ b) :
    (Finset.univ.filter (fun S : Finset α => a ∈ S ∧ b ∈ S)).card = 2 ^ (Fintype.card α - 2) ∧
    ∑ S ∈ Finset.univ.filter (fun S : Finset α => a ∈ S ∧ b ∈ S), S.card =
      (Fintype.card α - 2) * 2 ^ (Fintype.card α - 3) + 2 * 2 ^ (Fintype.card α - 2) := by
  classical
  let U := (Finset.univ.erase a).erase b
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm,Finset.mem_univ _⟩
  have hU : U.card = Fintype.card α - 2 := by
    rw [Finset.card_erase_of_mem hb,Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ]
    omega
  have hsize (t : Finset α) (ht : t ∈ U.powerset) :
      (insert a (insert b t)).card = t.card+2 := by
    have hsub := Finset.mem_powerset.mp ht
    have hnb : b ∉ t := fun hb => (Finset.mem_erase.mp (hsub hb)).1 rfl
    have hna : a ∉ insert b t := by
      simp only [Finset.mem_insert,not_or]
      exact ⟨hab,fun ha => (Finset.mem_erase.mp (Finset.mem_erase.mp (hsub ha)).2).1 rfl⟩
    rw [Finset.card_insert_of_notMem hna,Finset.card_insert_of_notMem hnb]
  constructor
  · rw [in148_filter_pair_mem_univ_eq_image a b hab,Finset.card_image_of_injOn (in148_insert_pair_injOn a b hab),
      Finset.card_powerset,hU]
  · rw [in148_filter_pair_mem_univ_eq_image a b hab,Finset.sum_image (in148_insert_pair_injOn a b hab)]
    change ∑ t ∈ U.powerset, (insert a (insert b t)).card = _
    rw [Finset.sum_congr rfl hsize,Finset.sum_add_distrib,
      simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_powerset,
      Finset.sum_const,Finset.card_powerset,hU]
    norm_num only [smul_eq_mul,Nat.sub_sub] <;> omega

/-- For n ≥ 8, the number of subsets of Fin n that induce a connected subgraph in simple_graph_clique_four_bridge_clique n is 5 * 2^(n-4) + 14, and the sum of their cardinalities is 32 + (n+24)*2^(n-5) + (n-5)*2^(n-3). -/
theorem simple_graph_clique_four_bridge_clique_connected_card_and_sum (n : ℕ) (hn : 8 ≤ n) :
    let G := simple_graph_clique_four_bridge_clique n
    haveI : DecidableRel G.Adj := Classical.decRel _
    haveI : ∀ S : Finset (Fin n), Decidable (G.induce (S : Set (Fin n))).Connected := fun _ => Classical.dec _
    (Finset.univ.filter (fun S : Finset (Fin n) => (G.induce (S : Set (Fin n))).Connected)).card =
      5 * 2 ^ (n - 4) + 14 ∧
    (Finset.univ.filter (fun S : Finset (Fin n) => (G.induce (S : Set (Fin n))).Connected)).sum Finset.card =
      32 + (n + 24) * 2 ^ (n - 5) + (n - 5) * 2 ^ (n - 3) := by
  classical
  dsimp only
  rw [Finset.filter_congr_decidable (s := Finset.univ)
    (p := fun S : Finset (Fin n) => (SimpleGraph.induce (↑S) (simple_graph_clique_four_bridge_clique n)).Connected)
    (Classical.decPred _)]
  set v3 : Fin n := ⟨3,by omega⟩ with hv3
  set v4 : Fin n := ⟨4,by omega⟩ with hv4
  have hv3val : v3.val = 3 := rfl
  have hv4val : v4.val = 4 := rfl
  have hv34 : v3 ≠ v4 := by intro he; have := congrArg Fin.val he; omega
  set L : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => x.val ≤ 3) with hL
  set R : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => 4 ≤ x.val) with hR
  set F1 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S : Finset (Fin n) =>
    S.Nonempty ∧ ∀ x ∈ S, x.val ≤ 3) with hF1
  set F2 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S : Finset (Fin n) =>
    S.Nonempty ∧ ∀ x ∈ S, 4 ≤ x.val) with hF2
  set F3 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S : Finset (Fin n) =>
    v3 ∈ S ∧ v4 ∈ S) with hF3
  have hT : Finset.univ.filter (fun S : Finset (Fin n) =>
      (SimpleGraph.induce (↑S) (simple_graph_clique_four_bridge_clique n)).Connected) = F1 ∪ (F2 ∪ F3) := by
    rw [hF1,hF2,hF3,← Finset.filter_or,← Finset.filter_or]
    exact Finset.filter_congr (fun S _ => in148_connected_iff n v3 v4 hv3val hv4val S)
  have hd23 : Disjoint F2 F3 := by
    apply Finset.disjoint_left.mpr
    intro S hS hS'
    simp only [hF2,hF3,Finset.mem_filter,Finset.mem_univ,true_and] at hS hS'
    have := hS.2 v3 hS'.1
    omega
  have hd1 : Disjoint F1 (F2 ∪ F3) := by
    apply Finset.disjoint_left.mpr
    intro S hS hS'
    simp only [hF1,Finset.mem_filter,Finset.mem_univ,true_and] at hS
    rcases Finset.mem_union.mp hS' with hS' | hS'
    · simp only [hF2,Finset.mem_filter,Finset.mem_univ,true_and] at hS'
      obtain ⟨x,hx⟩ := hS.1
      have := hS.2 x hx
      have := hS'.2 x hx
      omega
    · simp only [hF3,Finset.mem_filter,Finset.mem_univ,true_and] at hS'
      have := hS.2 v4 hS'.2
      omega
  have hF1eq : F1 = L.powerset.filter Finset.Nonempty := by
    rw [hF1,hL]
    ext S
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powerset,Finset.subset_iff]
    exact ⟨fun h => ⟨h.2,h.1⟩,fun h => ⟨h.2,h.1⟩⟩
  have hF2eq : F2 = R.powerset.filter Finset.Nonempty := by
    rw [hF2,hR]
    ext S
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powerset,Finset.subset_iff]
    exact ⟨fun h => ⟨h.2,h.1⟩,fun h => ⟨h.2,h.1⟩⟩
  have hLc : L.card = 4 := by rw [hL]; exact in148_card_filter_val_le_three n (by omega)
  have hRc : R.card = n-4 := by
    rw [hR]
    exact simple_graph_clique_four_glued_clique_connected_card_and_sum_card_filter_val_ge_four n (by omega)
  have hF1c : F1.card = 15 := by
    rw [hF1eq,simple_graph_clique_four_glued_clique_connected_card_and_sum_card_nonempty_powerset,hLc]
    norm_num
  have hF1s : ∑ S ∈ F1, S.card = 32 := by
    rw [hF1eq,simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_nonempty_powerset,hLc]
    norm_num
  have hF2c : F2.card = 2^(n-4)-1 := by
    rw [hF2eq,simple_graph_clique_four_glued_clique_connected_card_and_sum_card_nonempty_powerset,hRc]
  have hF2s : ∑ S ∈ F2, S.card = (n-4)*2^(n-5) := by
    rw [hF2eq,simple_graph_clique_four_glued_clique_connected_card_and_sum_sum_card_nonempty_powerset,hRc]
    rw [show n-4-1 = n-5 by omega]
  have hF3c : F3.card = 2^(n-2) := by
    simpa only [Fintype.card_fin] using (in148_pair_card_sum v3 v4 hv34).1
  have hF3s : ∑ S ∈ F3, S.card = (n-2)*2^(n-3)+2*2^(n-2) := by
    simpa only [Fintype.card_fin] using (in148_pair_card_sum v3 v4 hv34).2
  constructor
  · rw [hT,Finset.card_union_of_disjoint hd1,Finset.card_union_of_disjoint hd23,hF1c,hF2c,hF3c]
    have hp : 2^(n-2) = 4*2^(n-4) := by
      rw [show n-2 = (n-4)+2 by omega,pow_add]
      norm_num
      ring
    rw [hp]
    have hpos : 1 ≤ 2^(n-4) := Nat.one_le_two_pow
    omega
  · rw [hT,Finset.sum_union hd1,Finset.sum_union hd23,hF1s,hF2s,hF3s]
    have hp2 : 2^(n-2) = 8*2^(n-5) := by
      rw [show n-2 = (n-5)+3 by omega,pow_add]
      norm_num
      ring
    have hp3 : 2^(n-3) = 4*2^(n-5) := by
      rw [show n-3 = (n-5)+2 by omega,pow_add]
      norm_num
      ring
    rw [hp2,hp3,show n-4 = (n-5)+1 by omega,show n-2 = (n-5)+3 by omega,
      show n+24 = (n-5)+29 by omega]
    ring
