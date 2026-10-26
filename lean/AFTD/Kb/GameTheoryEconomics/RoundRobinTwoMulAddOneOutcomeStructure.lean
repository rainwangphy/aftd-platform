import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateSuccStep
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocCardEq
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocMono
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequenceGetElemEq
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# round_robin_two_mul_add_one_outcome_structure

Topic: fair_division   Node: ccff294b80bc

Provenance: helper lemma. step towards round_robin_two_mul_add_one_deviation_certificate

Round-Robin with n agents and 2n+1 goods, any reports: there are goods a2, a3 (agent 0's picks at turns n and 2n) and b1, b2 (agent i's two picks) such that agent 0's bundle is {its first-ranked good, a2, a3}, these three are distinct, agent i's bundle is {b1, b2} with b1 ≠ b2, and the two bundles have 3 and 2 goods.
-/

private lemma rt3_structure_idle_bundle {N G : Type*} [DecidableEq N] [DecidableEq G] [Fintype G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (a : N) {s t : ℕ}
    (hst : s ≤ t) (htl : t ≤ seq.length) (htm : t ≤ m)
    (hno : ∀ u, s ≤ u → u < t → seq[u]? ≠ some a) :
    (picking_prefix_state seq rank t).1 a = (picking_prefix_state seq rank s).1 a := by
  have haux : ∀ u, s ≤ u → u ≤ t →
      (picking_prefix_state seq rank u).1 a = (picking_prefix_state seq rank s).1 a := by
    intro u hsu
    induction u,hsu using Nat.le_induction with
    | base => intro _; rfl
    | succ u hsu ih =>
      intro hut
      have hi := ih (by omega)
      have hul : u < seq.length := by omega
      let b : N := seq[u]'hul
      have hget : seq[u]? = some b := List.getElem?_eq_getElem hul
      have hab : a ≠ b := by
        intro h
        exact hno u hsu (by omega) (hget.trans (congrArg some h.symm))
      obtain ⟨_,_,_,_,hother,_⟩ :=
        picking_prefix_state_succ_step seq rank u hul (by omega) b hget
      rw [hother a hab,hi]
  exact haux t hst le_rfl

private lemma rt3_structure_mod_cases (n u a : ℕ) (hn : 0 < n) (ha : a < n) (hu : u ≤ 2*n)
    (he : u%n = a) : u = a ∨ u = n+a ∨ (u = 2*n ∧ a = 0) := by
  by_cases h0 : u < n
  · rw [Nat.mod_eq_of_lt h0] at he
    exact Or.inl he
  · by_cases h1 : u < 2*n
    · have hnu : n ≤ u := by omega
      have hmod : u%n = u-n := by
        rw [Nat.mod_eq_sub_mod hnu,Nat.mod_eq_of_lt (by omega)]
      exact Or.inr (Or.inl (by omega))
    · have hut : u = 2*n := by omega
      have ham : a = 0 := by simpa [hut] using he.symm
      exact Or.inr (Or.inr ⟨hut,ham⟩)

private lemma rt3_structure_outcome_prefix {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (rank : N → Fin m ≃ G) (a : N) :
    picking_sequence_outcome seq rank a = (picking_prefix_state seq rank seq.length).1 a := by
  simp only [picking_sequence_outcome,picking_prefix_state,List.take_length]

/-- Round-Robin with 2n+1 goods: agent 0 ends with the three goods it picks at turns 0, n and 2n (three distinct goods, the first of which is its top-ranked one), and agent i ≠ 0 with the two goods it picks at turns i and n+i. -/
theorem round_robin_two_mul_add_one_outcome_structure (n : ℕ) [NeZero n]
    (rank : Fin n → Fin (2 * n + 1) ≃ Fin (2 * n + 1)) (i : Fin n) (hi : i ≠ 0) :
    ∃ a2 a3 b1 b2 : Fin (2 * n + 1),
      a2 ∉ (picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank n).2 ∧
      a2 ∈ (picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank (n + 1)).2 ∧
      a3 ∉ (picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank (2 * n)).2 ∧
      a3 ∈ (picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank (2 * n + 1)).2 ∧
      picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 =
        {rank 0 ⟨0, by omega⟩, a2, a3} ∧
      picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank i = {b1, b2} ∧
      rank 0 ⟨0, by omega⟩ ≠ a2 ∧ rank 0 ⟨0, by omega⟩ ≠ a3 ∧ a2 ≠ a3 ∧ b1 ≠ b2 ∧
      (picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0).card = 3 ∧
      (picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank i).card = 2 := by
  classical
  have hn := NeZero.pos n
  have hil := i.isLt
  have hip : 0 < i.val := by
    have hiz : i.val ≠ 0 := by
      intro h
      apply hi
      exact Fin.ext (by simpa using h)
    omega
  let seq := round_robin_sequence n (2*n+1)
  let st := fun s => picking_prefix_state seq rank s
  have hlen : seq.length = 2*n+1 := by simp [seq,round_robin_sequence]
  have step (s : ℕ) (a : Fin n) (hs : s < 2*n+1) (ha : s%n = a.val) :
      ∃ p, p ∉ (st s).2 ∧ (st (s+1)).2 = insert p (st s).2 ∧
        (st (s+1)).1 a = insert p ((st s).1 a) ∧
        (∀ b, b ≠ a → (st (s+1)).1 b = (st s).1 b) ∧
        ∃ k : Fin (2*n+1), rank a k = p ∧ ∀ j, j < k → rank a j ∈ (st s).2 := by
    have hget : seq[s]? = some a := by
      change (round_robin_sequence n (2*n+1))[s]? = some a
      rw [round_robin_sequence_getElem?_eq n (2*n+1) s hs]
      exact congrArg some (Fin.ext ha)
    exact picking_prefix_state_succ_step seq rank s (by omega) hs a hget
  have idle (s t : ℕ) (a : Fin n) (hst : s ≤ t) (ht : t ≤ 2*n+1)
      (hno : ∀ u, s ≤ u → u < t → u%n ≠ a.val) : (st t).1 a = (st s).1 a := by
    apply rt3_structure_idle_bundle seq rank a hst (by omega) ht
    intro u hus hut he
    have hget := round_robin_sequence_getElem?_eq n (2*n+1) u (by omega)
    change seq[u]? = some (⟨u%n,Nat.mod_lt _ hn⟩ : Fin n) at hget
    have hval : u%n = a.val := congrArg Fin.val (Option.some.inj (hget.symm.trans he))
    exact hno u hus hut hval
  have mono {s t : ℕ} (h : s ≤ t) : (st s).2 ⊆ (st t).2 :=
    picking_prefix_state_alloc_mono seq rank h
  have hout (a : Fin n) : picking_sequence_outcome seq rank a = (st (2*n+1)).1 a :=
    (rt3_structure_outcome_prefix seq rank a).trans
      (congrArg (fun t => (picking_prefix_state seq rank t).1 a) hlen)
  obtain ⟨p0,hp0free,hA0,hB0,_,k0,hk0,hbefore⟩ := step 0 0 (by omega) (by simp)
  have hp0 : p0 = rank 0 ⟨0,by omega⟩ := by
    have hkv : k0.val = 0 := by
      by_contra hne
      have hj : (⟨0,by omega⟩ : Fin (2*n+1)) < k0 := by
        change 0 < k0.val
        omega
      have hh := hbefore _ hj
      simpa [st,picking_prefix_state] using hh
    have hke : k0 = ⟨0,by omega⟩ := Fin.ext hkv
    simpa only [hke] using hk0.symm
  subst p0
  rw [hp0] at hA0 hB0
  obtain ⟨a2,hfree2,hA2,hB2,_,_⟩ := step n 0 (by omega) (by simp)
  obtain ⟨a3,hfree3,hA3,hB3,_,_⟩ := step (2*n) 0 (by omega) (by simp)
  obtain ⟨b1,hfreeb1,hAb1,hBb1,_,_⟩ := step i.val i (by omega) (Nat.mod_eq_of_lt hil)
  obtain ⟨b2,hfreeb2,hAb2,hBb2,_,_⟩ := step (n+i.val) i (by omega)
    (by simp [Nat.add_mod,Nat.mod_eq_of_lt hil])
  have h01 : (st n).1 0 = (st 1).1 0 := by
    apply idle 1 n 0 (by omega) (by omega)
    intro u hu1 hu2 he
    rcases rt3_structure_mod_cases n u 0 hn (by omega) (by omega) he with h | h | ⟨h,_⟩ <;> omega
  have h12 : (st (2*n)).1 0 = (st (n+1)).1 0 := by
    apply idle (n+1) (2*n) 0 (by omega) (by omega)
    intro u hu1 hu2 he
    rcases rt3_structure_mod_cases n u 0 hn (by omega) (by omega) he with h | h | ⟨h,_⟩ <;> omega
  have hi0 : (st i.val).1 i = (st 0).1 i := by
    apply idle 0 i.val i (by omega) (by omega)
    intro u hu1 hu2 he
    rcases rt3_structure_mod_cases n u i.val hn hil (by omega) he with h | h | ⟨h,hz⟩ <;> omega
  have hi1 : (st (n+i.val)).1 i = (st (i.val+1)).1 i := by
    apply idle (i.val+1) (n+i.val) i (by omega) (by omega)
    intro u hu1 hu2 he
    rcases rt3_structure_mod_cases n u i.val hn hil (by omega) he with h | h | ⟨h,hz⟩ <;> omega
  have hi2 : (st (2*n+1)).1 i = (st (n+i.val+1)).1 i := by
    apply idle (n+i.val+1) (2*n+1) i (by omega) (by omega)
    intro u hu1 hu2 he
    rcases rt3_structure_mod_cases n u i.val hn hil (by omega) he with h | h | ⟨h,hz⟩ <;> omega
  have hbzero : (st (2*n+1)).1 0 = {rank 0 ⟨0,by omega⟩,a2,a3} := by
    rw [hB3,h12,hB2,h01,hB0]
    ext g
    simp only [st,picking_prefix_state,List.take_zero,List.foldl_nil,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false]
    tauto
  have hbi : (st (2*n+1)).1 i = {b1,b2} := by
    rw [hi2,hBb2,hi1,hBb1,hi0]
    simp [st,picking_prefix_state,Finset.pair_comm]
  have hp0A : rank 0 ⟨0,by omega⟩ ∈ (st 1).2 := by rw [hA0]; simp
  have ha2A : a2 ∈ (st (n+1)).2 := by rw [hA2]; simp
  have ha3A : a3 ∈ (st (2*n+1)).2 := by rw [hA3]; simp
  have hb1A : b1 ∈ (st (i.val+1)).2 := by rw [hAb1]; simp
  have h02 : rank 0 ⟨0,by omega⟩ ≠ a2 := by
    intro he
    exact hfree2 (he ▸ mono (show 1 ≤ n by omega) hp0A)
  have h03 : rank 0 ⟨0,by omega⟩ ≠ a3 := by
    intro he
    exact hfree3 (he ▸ mono (show 1 ≤ 2*n by omega) hp0A)
  have h23 : a2 ≠ a3 := by
    intro he
    exact hfree3 (he ▸ mono (show n+1 ≤ 2*n by omega) ha2A)
  have hb12 : b1 ≠ b2 := by
    intro he
    exact hfreeb2 (he ▸ mono (show i.val+1 ≤ n+i.val by omega) hb1A)
  refine ⟨a2,a3,b1,b2,hfree2,ha2A,hfree3,ha3A,(hout 0).trans hbzero,
    (hout i).trans hbi,h02,h03,h23,hb12,?_,?_⟩
  · rw [hout 0,hbzero]
    have hz : rank 0 ⟨0,by omega⟩ ∉ ({a2,a3} : Finset (Fin (2*n+1))) := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using And.intro h02 h03
    rw [Finset.card_insert_of_notMem hz,Finset.card_pair h23]
  · rw [hout i,hbi]
    simp [hb12]
