import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinTwoMulAddOneWindowTrace
import AFTD.Kb.GameTheoryEconomics.PickingPrefixTwoNamedFirstDevBundle
import AFTD.Kb.GameTheoryEconomics.RoundRobinTwoMulAddOneOutcomeStructure
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateSuccStep
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocCardEq
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocMono
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequenceGetElemEq
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateUpdateOfNotMemTake
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# round_robin_two_mul_add_one_cover_pairs

Topic: fair_division   Node: d2de0b3e0429

Provenance: helper lemma. step towards round_robin_two_mul_add_one_deviation_certificate

Round-Robin with n agents and 2n+1 goods, agent i ≠ 0: let a1 be agent 0's top-ranked good, a2 and a3 the goods it picks at turns n and 2n, and let agent i's bundle be {b1, b2}. Then either some report of agent i alone gives it a bundle containing both a2 and a3, or two reports of agent i give bundles whose union contains a2, a3, b1 and b2.
-/

private lemma rt3_cover_window_congr {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (rank₁ rank₂ : N → Fin m ≃ G) (i : N) (s t : ℕ) (hst : s ≤ t)
    (hstart : picking_prefix_state seq rank₁ s = picking_prefix_state seq rank₂ s)
    (hr : ∀ a, a ≠ i → rank₁ a = rank₂ a)
    (hno : ∀ u, s ≤ u → u < t → seq[u]? ≠ some i) :
    picking_prefix_state seq rank₁ t = picking_prefix_state seq rank₂ t := by
  have haux : ∀ u, s ≤ u → u ≤ t →
      picking_prefix_state seq rank₁ u = picking_prefix_state seq rank₂ u := by
    intro u hsu
    induction u,hsu using Nat.le_induction with
    | base => intro _; exact hstart
    | succ u hsu ih =>
      intro hut
      have he := ih (by omega)
      rcases hg : seq[u]? with _ | a
      · rw [picking_prefix_two_named_first_dev_bundle_step_none seq rank₁ u hg,
          picking_prefix_two_named_first_dev_bundle_step_none seq rank₂ u hg,he]
      · have hai : a ≠ i := by
          intro hai
          exact hno u hsu (by omega) (hg.trans (congrArg some hai))
        rw [picking_prefix_two_named_first_dev_bundle_step seq rank₁ u a hg,
          picking_prefix_two_named_first_dev_bundle_step seq rank₂ u a hg,he,hr a hai]
  exact haux t hst le_rfl

private lemma rt3_cover_turn_first {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (r : Fin m ≃ G) (hm : 0 < m) (i : N) (st : (N → Finset G) × Finset G)
    (hfree : r ⟨0,hm⟩ ∉ st.2) :
    picking_turn (List.ofFn ⇑r) i st =
      (Function.update st.1 i (insert (r ⟨0,hm⟩) (st.1 i)),insert (r ⟨0,hm⟩) st.2) := by
  obtain ⟨k,rfl⟩ : ∃ k, m = k+1 := ⟨m-1,by omega⟩
  have h0 : (⟨0,hm⟩ : Fin (k+1)) = 0 := rfl
  rw [h0] at hfree ⊢
  rw [List.ofFn_succ]
  unfold picking_turn
  rw [List.find?_cons,decide_eq_true hfree]

private lemma rt3_cover_two_first (m : ℕ) (hm : 1 < m) (x y : Fin m) (hxy : x ≠ y) :
    ∃ r : Fin m ≃ Fin m, r ⟨0,by omega⟩ = x ∧ r ⟨1,hm⟩ = y := by
  let z : Fin m := ⟨0,by omega⟩
  let o : Fin m := ⟨1,hm⟩
  let e := Equiv.swap z x
  have hez : e z = x := Equiv.swap_apply_left _ _
  have hzo : z ≠ o := by intro h; have := congrArg Fin.val h; dsimp [z,o] at this; omega
  have heo : e o ≠ x := by
    intro he
    exact hzo (e.injective (he.trans hez.symm)).symm
  refine ⟨e.trans (Equiv.swap (e o) y),?_,?_⟩
  · change Equiv.swap (e o) y (e z) = x
    rw [hez,Equiv.swap_apply_of_ne_of_ne heo.symm hxy]
  · exact Equiv.swap_apply_left _ _

private lemma rt3_cover_state_ext {N G : Type*} [DecidableEq N] [DecidableEq G]
    (st st' : (N → Finset G) × Finset G) (i : N) (p : G)
    (hA : st'.2 = insert p st.2) (hB : st'.1 i = insert p (st.1 i))
    (hother : ∀ j, j ≠ i → st'.1 j = st.1 j) :
    st' = (Function.update st.1 i (insert p (st.1 i)),insert p st.2) := by
  apply Prod.ext
  · funext j
    by_cases hji : j = i
    · subst j; simpa using hB
    · simpa [Function.update_of_ne hji] using hother j hji
  · exact hA

private lemma rt3_cover_mem_final {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (rank : N → Fin m ≃ G) (i : N) (s : ℕ) (hs : s ≤ seq.length)
    (g : G) (hg : g ∈ (picking_prefix_state seq rank s).1 i) :
    g ∈ picking_sequence_outcome seq rank i := by
  have hh := (picking_prefix_two_named_first_dev_bundle_mono seq rank s seq.length hs).1 i hg
  simpa only [picking_prefix_state,List.take_length,picking_sequence_outcome] using hh

/-- The valuation-free cover for 2n+1 goods: either one deviation of agent i secures both of agent 0's remaining picks, or two deviations secure all four contested goods between them. -/
theorem round_robin_two_mul_add_one_cover_pairs (n : ℕ) [NeZero n]
    (rank : Fin n → Fin (2 * n + 1) ≃ Fin (2 * n + 1)) (i : Fin n) (hi : i ≠ 0)
    (a1 a2 a3 b1 b2 : Fin (2 * n + 1))
    (ha1 : a1 = rank 0 ⟨0, by omega⟩)
    (hp2 : a2 ∉ (picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank n).2 ∧
      a2 ∈ (picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank (n + 1)).2)
    (hp3 : a3 ∉ (picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank (2 * n)).2 ∧
      a3 ∈ (picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank (2 * n + 1)).2)
    (hB0 : picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 = {a1, a2, a3})
    (hBi : picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank i = {b1, b2})
    (hdist : a1 ≠ a2 ∧ a1 ≠ a3 ∧ a2 ≠ a3) :
    (∃ r : Fin (2 * n + 1) ≃ Fin (2 * n + 1),
        ({a2, a3} : Finset (Fin (2 * n + 1))) ⊆
          picking_sequence_outcome (round_robin_sequence n (2 * n + 1))
            (Function.update rank i r) i) ∨
    (∃ r₁ r₂ : Fin (2 * n + 1) ≃ Fin (2 * n + 1),
        ({a2, a3, b1, b2} : Finset (Fin (2 * n + 1))) ⊆
          picking_sequence_outcome (round_robin_sequence n (2 * n + 1))
            (Function.update rank i r₁) i ∪
          picking_sequence_outcome (round_robin_sequence n (2 * n + 1))
            (Function.update rank i r₂) i) := by
  classical
  have hn := NeZero.pos n
  have hil := i.isLt
  have hip : 0 < i.val := by
    have hz : i.val ≠ 0 := by
      intro h; apply hi; exact Fin.ext (by simpa using h)
    omega
  let seq := round_robin_sequence n (2*n+1)
  let st := fun (r : Fin n → Fin (2*n+1) ≃ Fin (2*n+1)) (s : ℕ) => picking_prefix_state seq r s
  let upd := fun (r : Fin (2*n+1) ≃ Fin (2*n+1)) => Function.update rank i r
  let out := fun (r : Fin (2*n+1) ≃ Fin (2*n+1)) => picking_sequence_outcome seq (upd r) i
  have hlen : seq.length = 2*n+1 := by simp [seq,round_robin_sequence]
  have ht1 : seq[i.val]? = some i := by
    rw [round_robin_sequence_getElem?_eq n (2*n+1) i.val (by omega)]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt hil)
  have ht2 : seq[n+i.val]? = some i := by
    rw [round_robin_sequence_getElem?_eq n (2*n+1) (n+i.val) (by omega)]
    congr 1
    exact Fin.ext (by simp [Nat.mod_eq_of_lt hil])
  have hno : ∀ u, i.val+1 ≤ u → u < n+i.val → seq[u]? ≠ some i := by
    intro u hu1 hu2 he
    have hg := round_robin_sequence_getElem?_eq n (2*n+1) u (by omega)
    have hv : u%n = i.val := congrArg Fin.val (Option.some.inj (hg.symm.trans he))
    exact round_robin_two_mul_add_one_window_trace_mod n u i.val hil (by omega) (by omega) hv
  have hpre (r : Fin (2*n+1) ≃ Fin (2*n+1)) : st (upd r) i.val = st rank i.val := by
    apply picking_prefix_state_update_of_not_mem_take
    intro hm
    obtain ⟨t,ht,he⟩ := List.getElem_of_mem hm
    rw [List.length_take] at ht
    rw [List.getElem_take] at he
    have hg := round_robin_sequence_getElem?_eq n (2*n+1) t (by omega)
    change seq[t]? = some (⟨t%n,Nat.mod_lt _ hn⟩ : Fin n) at hg
    rw [List.getElem?_eq_getElem (show t < seq.length by omega),he,Option.some_inj] at hg
    have hv := congrArg Fin.val hg
    simp only at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have first (r : Fin (2*n+1) ≃ Fin (2*n+1)) (x : Fin (2*n+1))
      (hx : x ∉ (st rank i.val).2) (hr : r ⟨0,by omega⟩ = x) :
      st (upd r) (i.val+1) =
        (Function.update (st rank i.val).1 i (insert x ((st rank i.val).1 i)),
          insert x (st rank i.val).2) := by
    have hs : st (upd r) (i.val+1) =
        picking_turn (List.ofFn ⇑((upd r) i)) i (st (upd r) i.val) :=
      picking_prefix_two_named_first_dev_bundle_step seq (upd r) i.val i ht1
    have hur : upd r i = r := Function.update_self i r rank
    rw [hs,hpre r,hur]
    change picking_turn (List.ofFn ⇑r) i (st rank i.val) = _
    simpa only [hr] using rt3_cover_turn_first r (by omega) i (st rank i.val) (by rw [hr]; exact hx)
  have together (r₁ r₂ : Fin (2*n+1) ≃ Fin (2*n+1))
      (he : st (upd r₁) (i.val+1) = st (upd r₂) (i.val+1)) :
      st (upd r₁) (n+i.val) = st (upd r₂) (n+i.val) := by
    apply rt3_cover_window_congr seq (upd r₁) (upd r₂) i (i.val+1) (n+i.val) (by omega) he
    · intro a ha; simp [upd,Function.update_of_ne ha]
    · exact hno
  obtain ⟨p,hpfree,hAp,hBp,hotherp,_⟩ :=
    picking_prefix_state_succ_step seq rank i.val (by omega) (by omega) i ht1
  obtain ⟨q,hqfree,hAq,hBq,_,_⟩ :=
    picking_prefix_state_succ_step seq rank (n+i.val) (by omega) (by omega) i ht2
  have hpA : p ∈ (st rank (i.val+1)).2 := by rw [hAp]; simp
  have hpq : p ≠ q := by
    intro he
    exact hqfree (he ▸ picking_prefix_state_alloc_mono seq rank (show i.val+1 ≤ n+i.val by omega) hpA)
  have hpmem : p ∈ picking_sequence_outcome seq rank i := by
    apply rt3_cover_mem_final seq rank i (i.val+1) (by omega) p
    rw [hBp]; simp
  have hqmem : q ∈ picking_sequence_outcome seq rank i := by
    apply rt3_cover_mem_final seq rank i (n+i.val+1) (by omega) q
    rw [hBq]; simp
  have hcard : (picking_sequence_outcome seq rank i).card ≤ 2 := by
    rw [hBi]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hset : ({p,q} : Finset (Fin (2*n+1))) = picking_sequence_outcome seq rank i := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      simp only [Finset.mem_insert,Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact hpmem
      · exact hqmem
    · rw [Finset.card_pair hpq]
      exact hcard
  have ha2free : a2 ∉ (st rank i.val).2 := by
    intro hh
    exact hp2.1 (picking_prefix_state_alloc_mono seq rank (show i.val ≤ n by omega) hh)
  have ha3free : a3 ∉ (st rank (n+i.val)).2 := by
    intro hh
    exact hp3.1 (picking_prefix_state_alloc_mono seq rank (show n+i.val ≤ 2*n by omega) hh)
  have hqy : q ≠ a3 := by
    intro he
    have hqA : q ∈ (st rank (n+i.val+1)).2 := by rw [hAq]; simp
    exact hp3.1 (he ▸ picking_prefix_state_alloc_mono seq rank (show n+i.val+1 ≤ 2*n by omega) hqA)
  have hpy : p ≠ a3 := by
    intro he
    exact hp3.1 (he ▸ picking_prefix_state_alloc_mono seq rank (show i.val+1 ≤ 2*n by omega) hpA)
  have ha2q : a2 ≠ q := by
    intro he
    exact hqfree (he ▸ picking_prefix_state_alloc_mono seq rank (show n+1 ≤ n+i.val by omega) hp2.2)
  obtain ⟨rxy,hrxy0,hrxy1⟩ := rt3_cover_two_first (2*n+1) (by omega) a2 a3 hdist.2.2
  by_cases hy : a3 ∉ (st (upd rxy) (n+i.val)).2
  · left
    exact ⟨rxy,picking_prefix_two_named_first_dev_bundle seq rank rxy i i.val (n+i.val)
      (by omega) (by omega) ht1 ht2 (by omega) a2 a3 ha2free hy hrxy0 hrxy1⟩
  · have hyA : a3 ∈ (st (upd rxy) (n+i.val)).2 := not_not.mp hy
    have hqD : q ∉ (st (upd rxy) (n+i.val)).2 := by
      intro hh
      have hc := (round_robin_two_mul_add_one_window_trace n rank i rxy (n+i.val)
        (by omega) (by omega)).1
      have he := Finset.card_le_one.mp hc a3 (Finset.mem_sdiff.mpr ⟨hyA,ha3free⟩)
        q (Finset.mem_sdiff.mpr ⟨hh,hqfree⟩)
      exact hqy he.symm
    obtain ⟨rxq,hrxq0,hrxq1⟩ := rt3_cover_two_first (2*n+1) (by omega) a2 q ha2q
    have hexy : st (upd rxq) (n+i.val) = st (upd rxy) (n+i.val) :=
      together rxq rxy ((first rxq a2 ha2free hrxq0).trans (first rxy a2 ha2free hrxy0).symm)
    have hxq : ({a2,q} : Finset (Fin (2*n+1))) ⊆ out rxq :=
      picking_prefix_two_named_first_dev_bundle seq rank rxq i i.val (n+i.val)
        (by omega) (by omega) ht1 ht2 (by omega) a2 q ha2free
        (by change q ∉ (st (upd rxq) (n+i.val)).2; rw [hexy]; exact hqD) hrxq0 hrxq1
    obtain ⟨rpy,hrpy0,hrpy1⟩ := rt3_cover_two_first (2*n+1) (by omega) p a3 hpy
    have heorig : st (upd rpy) (n+i.val) = st rank (n+i.val) := by
      apply rt3_cover_window_congr seq (upd rpy) rank i (i.val+1) (n+i.val) (by omega)
        ((first rpy p hpfree hrpy0).trans (rt3_cover_state_ext _ _ i p hAp hBp hotherp).symm)
      · intro a ha; simp [upd,Function.update_of_ne ha]
      · exact hno
    have hpyout : ({p,a3} : Finset (Fin (2*n+1))) ⊆ out rpy :=
      picking_prefix_two_named_first_dev_bundle seq rank rpy i i.val (n+i.val)
        (by omega) (by omega) ht1 ht2 (by omega) p a3 hpfree
        (by change a3 ∉ (st (upd rpy) (n+i.val)).2; rw [heorig]; exact ha3free) hrpy0 hrpy1
    right
    refine ⟨rxq,rpy,?_⟩
    have hbase : picking_sequence_outcome seq rank i ⊆ out rxq ∪ out rpy := by
      rw [← hset]
      intro g hg
      simp only [Finset.mem_insert,Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact Finset.mem_union_right _ (hpyout (by simp))
      · exact Finset.mem_union_left _ (hxq (by simp))
    intro g hg
    simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (hxq (by simp))
    · exact Finset.mem_union_right _ (hpyout (by simp))
    · exact hbase (by rw [hBi]; simp)
    · exact hbase (by rw [hBi]; simp)
