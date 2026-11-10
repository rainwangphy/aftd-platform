import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingReverseCrossoutValid
import AFTD.Kb.GameTheoryEconomics.PickingReverseCrossoutAllocation
import AFTD.Kb.GameTheoryEconomics.PickGameIsSpe
import AFTD.Kb.GameTheoryEconomics.PickGameRootAllocation
import AFTD.Kb.GameTheoryEconomics.PickGameMovePayoff
import AFTD.Kb.GameTheoryEconomics.PickGameMoveZero

/-!
# picking_two_agent_spe_eq_reverse_crossout

Topic: fair_division   Node: fb1fa97d754a

Provenance: formalization of a published result. Source: Strategic Behavior when Allocating Indivisible Goods Sequentially, Theorem 1, https://cdn.aaai.org/ojs/8697/8697-13-12225-1-2-20201228.pdf; expressed through history-dependent continuation profiles and positive additive values.

In a finite two-agent sequential picking game with any fixed order and positive additive item values distinct for each agent, every subgame-perfect continuation profile has the same root allocation as any valid reverse crossout sequence: reverse the picking order and repeatedly give the current picker a remaining item least valued by the other player.
-/

def pk2_oth (l : Fin 2) : Fin 2 := if l = 0 then 1 else 0

theorem pk2_fin2 (a : Fin 2) (h : a ≠ 0) : a = 1 := by
  fin_cases a <;> simp_all

theorem pk2_oth_of_ne (l p : Fin 2) (h : l ≠ p) : pk2_oth l = p := by
  fin_cases l <;> fin_cases p <;> simp_all [pk2_oth]

noncomputable def pk2_amin {α : Type*} [Nonempty α] (w : α → ℝ) (T : Finset α) : α :=
  Classical.epsilon (fun x => x ∈ T ∧ ∀ y ∈ T, w x ≤ w y)

theorem pk2_amin_spec {α : Type*} [Nonempty α] (w : α → ℝ) (T : Finset α) (hT : T.Nonempty) :
    pk2_amin w T ∈ T ∧ ∀ y ∈ T, w (pk2_amin w T) ≤ w y := by
  obtain ⟨x, hx, hmin⟩ := T.exists_min_image w hT
  exact Classical.epsilon_spec (p := fun x => x ∈ T ∧ ∀ y ∈ T, w x ≤ w y) ⟨x, hx, hmin⟩

theorem pk2_amin_eq {α : Type*} [Nonempty α] (w : α → ℝ) (hw : Function.Injective w)
    (T : Finset α) (x : α) (hx : x ∈ T) (hmin : ∀ y ∈ T, w x ≤ w y) : pk2_amin w T = x := by
  have h := pk2_amin_spec w T ⟨x, hx⟩
  exact hw (le_antisymm (h.2 x hx) (hmin _ h.1))

theorem pk2_amin_erase {α : Type*} [DecidableEq α] [Nonempty α] (w : α → ℝ)
    (hw : Function.Injective w) (T : Finset α) (hT : T.Nonempty) (z : α)
    (hz : z ≠ pk2_amin w T) : pk2_amin w (T.erase z) = pk2_amin w T := by
  have h := pk2_amin_spec w T hT
  exact pk2_amin_eq w hw _ _ (Finset.mem_erase.mpr ⟨fun h' => hz h'.symm, h.1⟩)
    (fun y hy => h.2 y (Finset.mem_of_mem_erase hy))

noncomputable def pk2_co {α : Type*} [DecidableEq α] [Nonempty α] (u : Fin 2 → α → ℝ) :
    List (Fin 2) → Finset α → Fin 2 → Finset α
  | [], _, _ => ∅
  | l :: r, T, i => (if l = i then {pk2_amin (u (pk2_oth l)) T} else ∅) ∪
      pk2_co u r (T.erase (pk2_amin (u (pk2_oth l)) T)) i

noncomputable def pk2_lo {α : Type*} [DecidableEq α] [Nonempty α] (u : Fin 2 → α → ℝ) :
    List (Fin 2) → Finset α → α
  | [], T => Classical.epsilon (· ∈ T)
  | l :: r, T => pk2_lo u r (T.erase (pk2_amin (u (pk2_oth l)) T))

section
variable {α : Type*} [DecidableEq α] [Nonempty α] (u : Fin 2 → α → ℝ)

theorem pk2_co_subset : ∀ (r : List (Fin 2)) (T : Finset α) (i : Fin 2),
    r.length ≤ T.card → pk2_co u r T i ⊆ T
  | [], T, i, _ => by simp [pk2_co]
  | l :: r, T, i, h => by
      have hT : T.Nonempty := Finset.card_pos.mp (by simp at h; omega)
      have he := (pk2_amin_spec (u (pk2_oth l)) T hT).1
      have ih := pk2_co_subset r (T.erase (pk2_amin (u (pk2_oth l)) T)) i
        (by rw [Finset.card_erase_of_mem he]; simp at h; omega)
      simp only [pk2_co]
      apply Finset.union_subset
      · split_ifs <;> simp [he]
      · exact ih.trans (Finset.erase_subset _ _)

theorem pk2_co_disj : ∀ (r : List (Fin 2)) (T : Finset α),
    r.length ≤ T.card → Disjoint (pk2_co u r T 0) (pk2_co u r T 1)
  | [], T, _ => by simp [pk2_co]
  | l :: r, T, h => by
      have hT : T.Nonempty := Finset.card_pos.mp (by simp at h; omega)
      simp only [pk2_co]
      set e := pk2_amin (u (pk2_oth l)) T
      have he : e ∈ T := (pk2_amin_spec (u (pk2_oth l)) T hT).1
      have hc : r.length ≤ (T.erase e).card := by
        rw [Finset.card_erase_of_mem he]; simp at h; omega
      have ih := pk2_co_disj r (T.erase e) hc
      have s0 := pk2_co_subset u r (T.erase e) 0 hc
      have s1 := pk2_co_subset u r (T.erase e) 1 hc
      have n0 : e ∉ pk2_co u r (T.erase e) 0 := fun h' => by simpa using s0 h'
      have n1 : e ∉ pk2_co u r (T.erase e) 1 := fun h' => by simpa using s1 h'
      have hl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
      rcases hl with rfl | rfl <;>
        simp [Finset.disjoint_union_left, Finset.disjoint_union_right, ih, n0, n1]

theorem pk2_co_union : ∀ (r : List (Fin 2)) (T : Finset α),
    r.length = T.card → pk2_co u r T 0 ∪ pk2_co u r T 1 = T
  | [], T, h => by simp at h; simp [pk2_co, Finset.card_eq_zero.mp h.symm]
  | l :: r, T, h => by
      have hT : T.Nonempty := Finset.card_pos.mp (by simp at h; omega)
      simp only [pk2_co]
      set e := pk2_amin (u (pk2_oth l)) T
      have he : e ∈ T := (pk2_amin_spec (u (pk2_oth l)) T hT).1
      have hc : r.length = (T.erase e).card := by
        rw [Finset.card_erase_of_mem he]; simp at h; omega
      have ih := pk2_co_union r (T.erase e) hc
      have key : insert e (T.erase e) = T := Finset.insert_erase he
      have hl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
      rcases hl with rfl | rfl
      · simp only [if_true, show ¬ ((0 : Fin 2) = 1) by decide, if_false, Finset.empty_union]
        rw [Finset.union_assoc, ih, ← Finset.insert_eq, key]
      · simp only [if_true, show ¬ ((1 : Fin 2) = 0) by decide, if_false, Finset.empty_union]
        rw [Finset.union_left_comm, ih, ← Finset.insert_eq, key]

theorem pk2_lo_mem : ∀ (r : List (Fin 2)) (T : Finset α),
    T.card = r.length + 1 → pk2_lo u r T ∈ T
  | [], T, h => by
      simp only [pk2_lo]
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by simpa using h)
      exact Classical.epsilon_spec (p := (· ∈ T)) ⟨a, by simp [ha]⟩
  | l :: r, T, h => by
      have hT : T.Nonempty := Finset.card_pos.mp (by omega)
      have he := (pk2_amin_spec (u (pk2_oth l)) T hT).1
      simp only [pk2_lo]
      exact Finset.mem_of_mem_erase (pk2_lo_mem r _ (by rw [Finset.card_erase_of_mem he]; simp at h ⊢; omega))

variable (hinj : ∀ j, Function.Injective (u j))
include hinj

theorem pk2_co_append (p : Fin 2) : ∀ (r : List (Fin 2)) (T : Finset α) (i : Fin 2),
    T.card = r.length + 1 →
    pk2_co u (r ++ [p]) T i = pk2_co u r (T.erase (pk2_lo u r T)) i ∪
      (if p = i then {pk2_lo u r T} else ∅)
  | [], T, i, h => by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by simpa using h)
      subst ha
      have h1 : pk2_amin (u (pk2_oth p)) {a} = a := by
        have := (pk2_amin_spec (u (pk2_oth p)) {a} (by simp)).1
        simpa using this
      have h2 : pk2_lo u [] {a} = a := by
        simp only [pk2_lo]
        have := Classical.epsilon_spec (p := (· ∈ ({a} : Finset α))) ⟨a, by simp⟩
        simpa using this
      simp [pk2_co, h1, h2]
  | l :: r, T, i, h => by
      have hT : T.Nonempty := Finset.card_pos.mp (by omega)
      set e := pk2_amin (u (pk2_oth l)) T with he_def
      have he : e ∈ T := (pk2_amin_spec (u (pk2_oth l)) T hT).1
      have hc : (T.erase e).card = r.length + 1 := by
        rw [Finset.card_erase_of_mem he]; simp at h; omega
      have ih := pk2_co_append p r (T.erase e) i hc
      have hL : pk2_lo u (l :: r) T = pk2_lo u r (T.erase e) := by simp only [pk2_lo, e]
      have hLmem := pk2_lo_mem u r (T.erase e) hc
      have hLe : pk2_lo u r (T.erase e) ≠ e := (Finset.mem_erase.mp hLmem).1
      have hamin : pk2_amin (u (pk2_oth l)) (T.erase (pk2_lo u r (T.erase e))) = e :=
        pk2_amin_erase _ (hinj _) T hT _ hLe
      rw [List.cons_append]
      simp only [pk2_co]
      rw [← he_def, ih, hL, hamin, Finset.erase_right_comm, Finset.union_assoc]

/-- the mover's bundle after choosing `y` with the crossout continuation -/
noncomputable def pk2_B (r : List (Fin 2)) (T : Finset α) (p : Fin 2) (y : α) : Finset α :=
  insert y (pk2_co u r (T.erase y) p)

omit hinj in
theorem pk2_B_sub (r : List (Fin 2)) (T : Finset α) (p : Fin 2) (y : α) (hy : y ∈ T)
    (h : T.card = r.length + 1) : pk2_B u r T p y ⊆ T ∧ y ∉ pk2_co u r (T.erase y) p := by
  have hs := pk2_co_subset u r (T.erase y) p (by rw [Finset.card_erase_of_mem hy]; omega)
  refine ⟨Finset.insert_subset hy (hs.trans (Finset.erase_subset _ _)), fun h' => by simpa using hs h'⟩

theorem pk2_exchange (p : Fin 2) : ∀ (r : List (Fin 2)) (T : Finset α) (y : α),
    T.card = r.length + 1 → y ∈ T →
    (∑ z ∈ pk2_B u r T p y, u p z) < (∑ z ∈ pk2_B u r T p (pk2_lo u r T), u p z) ∨
      pk2_B u r T p y = pk2_B u r T p (pk2_lo u r T)
  | [], T, y, h, hy => by
      right
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by simpa using h)
      subst ha
      have h2 : pk2_lo u [] {a} = a := by
        simp only [pk2_lo]
        have := Classical.epsilon_spec (p := (· ∈ ({a} : Finset α))) ⟨a, by simp⟩
        simpa using this
      rw [h2, Finset.mem_singleton.mp hy]
  | l :: r, T, y, h, hy => by
      have hT : T.Nonempty := ⟨y, hy⟩
      set e := pk2_amin (u (pk2_oth l)) T with he_def
      have hspec := pk2_amin_spec (u (pk2_oth l)) T hT
      have he : e ∈ T := hspec.1
      set T' := T.erase e with hT'
      have hc : T'.card = r.length + 1 := by
        rw [hT', Finset.card_erase_of_mem he]; simp at h; omega
      set L := pk2_lo u r T' with hLdef
      have hL : pk2_lo u (l :: r) T = L := by simp only [pk2_lo, e, T', L]
      have hLmem : L ∈ T' := pk2_lo_mem u r T' hc
      have hLe : L ≠ e := (Finset.mem_erase.mp hLmem).1
      -- B for an item z ≠ e
      have hBz : ∀ z ∈ T, z ≠ e → pk2_B u (l :: r) T p z =
          if l = p then insert e (pk2_B u r T' p z) else pk2_B u r T' p z := by
        intro z hz hze
        have ham : pk2_amin (u (pk2_oth l)) (T.erase z) = e :=
          pk2_amin_erase _ (hinj _) T hT _ hze
        simp only [pk2_B, pk2_co, ham]
        rw [Finset.erase_right_comm]
        split_ifs
        · rw [Finset.singleton_union, Finset.insert_comm]
        · rw [Finset.empty_union]
      have hBsub : ∀ z ∈ T', pk2_B u r T' p z ⊆ T' := fun z hz => (pk2_B_sub u r T' p z hz hc).1
      have heB : ∀ z ∈ T', e ∉ pk2_B u r T' p z := fun z hz h' => by
        have := hBsub z hz h'; simp [T'] at this
      rw [hL, hBz L (Finset.mem_of_mem_erase hLmem) hLe]
      by_cases hye : y ≠ e
      · have hyT' : y ∈ T' := Finset.mem_erase.mpr ⟨hye, hy⟩
        rw [hBz y hy hye]
        rcases pk2_exchange p r T' y hc hyT' with hlt | heq
        · left
          split_ifs
          · rw [Finset.sum_insert (heB y hyT'), Finset.sum_insert (heB L hLmem)]; linarith
          · exact hlt
        · right; rw [heq]
      · push Not at hye
        subst hye
        set e' := pk2_amin (u (pk2_oth l)) T' with he'_def
        have hT'ne : T'.Nonempty := ⟨L, hLmem⟩
        have he' : e' ∈ T' := (pk2_amin_spec (u (pk2_oth l)) T' hT'ne).1
        have hBe : pk2_B u (l :: r) T p e =
            insert e (if l = p then pk2_B u r T' p e' else pk2_co u r (T'.erase e') p) := by
          simp only [pk2_B, pk2_co, ← hT', ← he'_def]
          split_ifs
          · rw [Finset.singleton_union]
          · rw [Finset.empty_union]
        rw [hBe]
        by_cases hlp : l = p
        · simp only [hlp, if_true]
          by_cases he'L : e' = L
          · right; rw [he'L]
          · have he'T : e' ∈ T' := he'
            rcases pk2_exchange p r T' e' hc he'T with hlt | heq
            · left
              rw [Finset.sum_insert (heB e' he'T), Finset.sum_insert (heB L hLmem)]; linarith
            · right; rw [heq]
        · simp only [hlp, if_false]
          have hop : pk2_oth l = p := pk2_oth_of_ne l p hlp
          left
          have he'sub := pk2_B_sub u r T' p e' he' hc
          have heco : e ∉ pk2_co u r (T'.erase e') p := fun h' => by
            have := pk2_co_subset u r (T'.erase e') p
              (by rw [Finset.card_erase_of_mem he']; omega) h'
            simp [T'] at this
          rw [Finset.sum_insert heco]
          have hlt1 : u p e < u p e' := by
            have hle : u (pk2_oth l) e ≤ u (pk2_oth l) e' := hspec.2 e' (Finset.mem_of_mem_erase he')
            rw [hop] at hle
            have hne : e' ≠ e := (Finset.mem_erase.mp he').1
            exact lt_of_le_of_ne hle (fun h' => hne ((hinj p) h').symm)
          have hB' : (∑ z ∈ pk2_B u r T' p e', u p z) =
              u p e' + ∑ z ∈ pk2_co u r (T'.erase e') p, u p z := by
            rw [pk2_B, Finset.sum_insert he'sub.2]
          have hle2 : (∑ z ∈ pk2_B u r T' p e', u p z) ≤ ∑ z ∈ pk2_B u r T' p L, u p z := by
            rcases pk2_exchange p r T' e' hc he' with hlt | heq
            · exact hlt.le
            · rw [heq]
          linarith
end

section
variable {α : Type*} [DecidableEq α] [Nonempty α] (u : Fin 2 → α → ℝ)

theorem pk2_compl (r : List (Fin 2)) (T : Finset α) (h : r.length = T.card) :
    T \ pk2_co u r T 0 = pk2_co u r T 1 ∧ T \ pk2_co u r T 1 = pk2_co u r T 0 := by
  have hu := pk2_co_union u r T h
  have hd := pk2_co_disj u r T h.le
  have e0 : T \ pk2_co u r T 0 = (pk2_co u r T 0 ∪ pk2_co u r T 1) \ pk2_co u r T 0 := by
    rw [hu]
  have e1 : T \ pk2_co u r T 1 = (pk2_co u r T 0 ∪ pk2_co u r T 1) \ pk2_co u r T 1 := by
    rw [hu]
  constructor
  · rw [e0, Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hd.symm]
  · rw [e1, Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hd]

theorem pk2_co0_eq (r : List (Fin 2)) (T : Finset α) (y : α) (hy : y ∈ T)
    (h : T.card = r.length + 1) :
    pk2_co u r (T.erase y) 0 = T \ pk2_B u r T 1 y := by
  have hc : r.length = (T.erase y).card := by rw [Finset.card_erase_of_mem hy]; omega
  rw [pk2_B, Finset.sdiff_insert, ← Finset.erase_sdiff_comm, (pk2_compl u r _ hc).2]

theorem pk2_sdiff_co0 (r : List (Fin 2)) (T : Finset α) (y : α) (hy : y ∈ T)
    (h : T.card = r.length + 1) :
    T \ pk2_co u r (T.erase y) 0 = pk2_B u r T 1 y := by
  have hc : r.length = (T.erase y).card := by rw [Finset.card_erase_of_mem hy]; omega
  have hs := pk2_co_subset u r (T.erase y) 0 hc.le
  have hy0 : y ∉ pk2_co u r (T.erase y) 0 := fun h' => by simpa using hs h'
  have e : T \ pk2_co u r (T.erase y) 0 = insert y (T.erase y) \ pk2_co u r (T.erase y) 0 := by
    rw [Finset.insert_erase hy]
  rw [e, Finset.insert_sdiff_of_notMem _ hy0, (pk2_compl u r _ hc).1, pk2_B]
end

theorem pk2_spe_eq {n : ℕ} [Nonempty (Fin n)] (u : Fin 2 → Fin n → ℝ)
    (hinj : ∀ j, Function.Injective (u j)) (s : List (Fin 2))
    (F : List (Fin n) → Finset (Fin n)) (hF : pick_game_is_spe u s F) :
    ∀ k, ∀ h : List (Fin n), h.Nodup → h.length + k = n →
      F h = pk2_co u (s.drop h.length).reverse (Finset.univ \ h.toFinset) 0 := by
  have hs : s.length = n := hF.1
  intro k
  induction k with
  | zero =>
      intro h hnd hlen
      have hspe := hF.2 h hnd
      simp only at hspe
      have hcard : h.toFinset.card = n := by rw [List.toFinset_card_of_nodup hnd]; omega
      have huniv : h.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hcard)
      rw [huniv, Finset.sdiff_self] at hspe ⊢
      rw [if_neg (by simp)] at hspe
      rw [hspe.2, List.drop_eq_nil_of_le (by omega)]
      simp [pk2_co]
  | succ k ih =>
      intro h hnd hlen
      have hspe := hF.2 h hnd
      simp only at hspe
      set R := Finset.univ \ h.toFinset with hR
      have hRcard : R.card = k + 1 := by
        rw [hR, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin, List.toFinset_card_of_nodup hnd]
        omega
      have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨-, hif⟩ := hspe
      rw [if_pos hRne] at hif
      obtain ⟨x, hxR, hFx, hmax⟩ := hif
      have hlt : h.length < s.length := by omega
      set p := s.getD h.length 0 with hp
      have hp' : s[h.length] = p := by rw [hp, List.getD_eq_getElem _ _ hlt]
      set r' := (s.drop (h.length + 1)).reverse with hr'
      have hr'len : r'.length = k := by simp [hr']; omega
      have hdrop : (s.drop h.length).reverse = r' ++ [p] := by
        rw [List.drop_eq_getElem_cons hlt, List.reverse_cons, hp']
      -- continuation after each move
      have hcont : ∀ y ∈ R, F (h ++ [y]) = pk2_co u r' (R.erase y) 0 := by
        intro y hy
        have hyh : y ∉ h := by simpa [hR] using hy
        have hnd' : (h ++ [y]).Nodup :=
          hnd.append (List.nodup_singleton y) (List.disjoint_singleton.mpr hyh)
        rw [ih (h ++ [y]) hnd' (by simp only [List.length_append, List.length_singleton]; omega)]
        congr 1
        · simp [hr']
        · rw [hR, List.toFinset_append]; ext z; simp
      have hpay : ∀ y ∈ R, pick_game_move_payoff u s F h y = ∑ z ∈ pk2_B u r' R p y, u p z := by
        intro y hy
        simp only [pick_game_move_payoff, pick_game_move_zero, ← hp, ← hR, hcont y hy]
        by_cases hp0 : p = 0
        · simp only [hp0, if_true, pk2_B]
        · have hp1 : p = 1 := pk2_fin2 p hp0
          simp only [hp0, if_false]
          rw [pk2_sdiff_co0 u r' R y hy (by omega), hp1]
      set L := pk2_lo u r' R
      have hLmem : L ∈ R := pk2_lo_mem u r' R (by omega)
      have hB : pk2_B u r' R p x = pk2_B u r' R p L := by
        rcases pk2_exchange u hinj p r' R x (by omega) hxR with hlt' | heq
        · have := hmax L hLmem
          rw [hpay L hLmem, hpay x hxR] at this
          linarith
        · exact heq
      rw [hFx, hdrop, pk2_co_append u hinj p r' R 0 (by omega)]
      simp only [pick_game_move_zero, ← hp, hcont x hxR]
      by_cases hp0 : p = 0
      · have := hB
        simp only [hp0, pk2_B] at this
        simp only [hp0, if_true]
        rw [this, Finset.union_comm, ← Finset.insert_eq]
      · have hp1 : p = 1 := pk2_fin2 p hp0
        simp only [hp0, if_false, Finset.union_empty]
        rw [pk2_co0_eq u r' R x hxR (by omega), pk2_co0_eq u r' R L hLmem (by omega), ← hp1, hB]

theorem pk2_crossout_link {n : ℕ} [Nonempty (Fin n)] (u : Fin 2 → Fin n → ℝ)
    (hinj : ∀ j, Function.Injective (u j)) (s : List (Fin 2)) (π : Fin n → Fin n)
    (hπ : picking_reverse_crossout_valid u s π) (i : Fin 2) :
    ∀ m, m ≤ n →
      pk2_co u (s.reverse.drop (n - m))
          ((Finset.univ.filter fun t : Fin n => n - m ≤ t.val).image π) i =
        (Finset.univ.filter fun t : Fin n => n - m ≤ t.val ∧ s.reverse.getD t.val 0 = i).image π := by
  obtain ⟨hs, hbij, hval⟩ := hπ
  have hrl : s.reverse.length = n := by simp [hs]
  intro m
  induction m with
  | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by omega)]
      have : (Finset.univ.filter fun t : Fin n => n ≤ t.val ∧ s.reverse.getD t.val 0 = i) = ∅ := by
        ext t; simp
      rw [this]; simp [pk2_co]
  | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      set t0 := n - (m + 1) with ht0
      have ht0lt : t0 < n := by omega
      set T0 : Fin n := ⟨t0, ht0lt⟩
      have hdrop : s.reverse.drop t0 = s.reverse[t0] :: s.reverse.drop (n - m) := by
        rw [List.drop_eq_getElem_cons (by omega)]; congr 2; omega
      have hget : s.reverse.getD t0 0 = s.reverse[t0] := List.getD_eq_getElem _ _ (by omega)
      set T := (Finset.univ.filter fun t : Fin n => t0 ≤ t.val).image π with hT
      have hamin : pk2_amin (u (pk2_oth s.reverse[t0])) T = π T0 := by
        apply pk2_amin_eq _ (hinj _)
        · exact Finset.mem_image.mpr ⟨T0, by simp [T0], rfl⟩
        · intro y hy
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rcases Nat.eq_or_lt_of_le hj with h' | h'
          · have : T0 = j := Fin.ext h'
            rw [this]
          · have := hval T0 j (by simp [Fin.lt_def, T0]; omega)
            simp only [T0] at this
            rw [hget] at this
            simpa [pk2_oth] using this
      have herase : T.erase (π T0) =
          (Finset.univ.filter fun t : Fin n => n - m ≤ t.val).image π := by
        rw [hT, ← Finset.image_erase hbij.1]
        congr 1
        ext t; simp [Fin.ext_iff, T0]; omega
      rw [hdrop]
      simp only [pk2_co]
      rw [hamin, herase, ih']
      ext z
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hz | ⟨t, ⟨ht1, ht2⟩, rfl⟩)
        · split_ifs at hz with hi
          · rw [Finset.mem_singleton] at hz
            exact ⟨T0, ⟨le_refl _, by show s.reverse.getD t0 0 = i; rw [hget, hi]⟩, hz.symm⟩
          · simp at hz
        · exact ⟨t, ⟨by omega, ht2⟩, rfl⟩
      · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
        rcases Nat.eq_or_lt_of_le ht1 with h' | h'
        · left
          have : T0 = t := Fin.ext h'
          subst this
          have hi : s.reverse[t0] = i := by rw [← hget]; exact ht2
          simp [hi]
        · right; exact ⟨t, ⟨by omega, ht2⟩, rfl⟩

theorem picking_two_agent_spe_eq_reverse_crossout (n : ℕ) (u : Fin 2 → Fin n → ℝ) (s : List (Fin 2))
  (π : Fin n → Fin n) (F : List (Fin n) → Finset (Fin n))
  (hu : ∀ i x, 0 < u i x) (hd : ∀ i x y, x ≠ y → u i x ≠ u i y)
  (hπ : picking_reverse_crossout_valid u s π) (hF : pick_game_is_spe u s F) :
  picking_reverse_crossout_allocation s π = pick_game_root_allocation F := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext i; ext x; exact x.elim0
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : ∀ j, Function.Injective (u j) := fun j x y hxy => by
    by_contra hne; exact hd j x y hne hxy
  have hs : s.length = n := hπ.1
  have hroot := pk2_spe_eq u hinj s F hF n [] List.nodup_nil (by simp)
  simp only [List.length_nil, List.drop_zero, List.toFinset_nil, Finset.sdiff_empty] at hroot
  have hlink := pk2_crossout_link u hinj s π hπ
  funext i
  have hl := hlink i n le_rfl
  simp only [Nat.sub_self, List.drop_zero, zero_le, true_and, Finset.filter_true_of_mem,
    Finset.mem_univ, implies_true] at hl
  rw [Finset.image_univ_of_surjective hπ.2.1.2] at hl
  unfold picking_reverse_crossout_allocation pick_game_root_allocation
  rw [← hl]
  split_ifs with hi
  · subst hi; exact hroot.symm
  · have hi1 : i = 1 := pk2_fin2 i hi
    subst hi1
    rw [hroot, (pk2_compl u s.reverse Finset.univ (by simp [hs])).1]
