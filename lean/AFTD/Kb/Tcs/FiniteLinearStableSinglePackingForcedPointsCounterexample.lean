import AFTD.Prelude

/-!
# finite_linear_stable_single_packing_forced_points_counterexample

Topic: graphs   Node: b972050debfa

Provenance: helper lemma. Exact construction and independent enumerations in experiments 16105–16106 and 16108; motivates graph completion in the triangle packing-cover campaign.

There is a stable linear three-uniform family with maximum packing P of size three, at most one singly forced point on each packed triple, and no non-book five-clique, such that no cover of size six is contained in the union of P. Nevertheless the family has a cover of size five.
-/

def sf667c {α : Type} (c : α → α → Bool) : ℕ → List α → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, t :: l => max (sf667c c n l) (1 + sf667c c n (l.filter (c t)))

theorem sf667c_bound {α : Type} [DecidableEq α] (c : α → α → Bool) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ S : Finset α, (∀ a ∈ S, a ∈ l) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → c a b = true) → S.card ≤ sf667c c n l := by
  intro n
  induction n with
  | zero =>
    intro l hl S hS _
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst hl0
    have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
    simp [this, sf667c]
  | succ n ih =>
    intro l hl S hS hc
    match l, hl, hS with
    | [], _, hS =>
      have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
      simp [this, sf667c]
    | t :: l, hl, hS =>
      rw [sf667c]
      by_cases ht : t ∈ S
      · refine le_trans ?_ (le_max_right _ _)
        have hsub : ∀ a ∈ S.erase t, a ∈ l.filter (c t) := by
          intro a ha
          have hne : a ≠ t := (Finset.mem_erase.mp ha).1
          have haS : a ∈ S := (Finset.mem_erase.mp ha).2
          have ha' : a ∈ t :: l := hS a haS
          have hal : a ∈ l := by
            rcases List.mem_cons.mp ha' with h | h
            · exact absurd h hne
            · exact h
          exact List.mem_filter.mpr ⟨hal, hc t ht a haS (Ne.symm hne)⟩
        have hlen : (l.filter (c t)).length ≤ n := by
          have := List.length_filter_le (c t) l
          simp only [List.length_cons] at hl
          omega
        have := ih (l.filter (c t)) hlen (S.erase t) hsub
          (fun a ha b hb hab => hc a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2 hab)
        have hcard := Finset.card_erase_add_one ht
        omega
      · refine le_trans ?_ (le_max_left _ _)
        have hlen : l.length ≤ n := by simpa using hl
        refine ih l hlen S ?_ hc
        intro a ha
        rcases List.mem_cons.mp (hS a ha) with h | h
        · exact absurd (h ▸ ha) ht
        · exact h

def sf667e {E : Type} [DecidableEq E] : ℕ → List (List E) → List (List E)
  | _, [] => [[]]
  | 0, _ :: _ => []
  | k + 1, l :: F => l.flatMap fun e => (sf667e k (F.filter fun l' => decide (e ∉ l'))).map (e :: ·)

theorem sf667e_complete {E : Type} [DecidableEq E] :
    ∀ (k : ℕ) (F : List (List E)) (D : Finset E), (∀ l ∈ F, ∃ e ∈ D, e ∈ l) → D.card ≤ k →
      ∃ s ∈ sf667e k F, s.toFinset ⊆ D := by
  intro k
  induction k with
  | zero =>
    intro F D hD hc
    match F, hD with
    | [], _ => exact ⟨[], by simp [sf667e], by simp⟩
    | l :: F, hD =>
      obtain ⟨e, he, _⟩ := hD l (by simp)
      have : D = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [this] at he
  | succ k ih =>
    intro F D hD hc
    match F, hD with
    | [], _ => exact ⟨[], by simp [sf667e], by simp⟩
    | l :: F, hD =>
      obtain ⟨e, he, hel⟩ := hD l (by simp)
      have hD' : ∀ l' ∈ F.filter (fun l' => decide (e ∉ l')), ∃ e' ∈ D.erase e, e' ∈ l' := by
        intro l' hl'
        have hmem := List.mem_filter.mp hl'
        obtain ⟨e', he', hel'⟩ := hD l' (List.mem_cons_of_mem _ hmem.1)
        refine ⟨e', Finset.mem_erase.mpr ⟨?_, he'⟩, hel'⟩
        rintro rfl
        have : e' ∉ l' := by simpa using hmem.2
        exact this hel'
      have hcard : (D.erase e).card ≤ k := by
        have := Finset.card_erase_add_one he
        omega
      obtain ⟨s, hs, hsD⟩ := ih _ _ hD' hcard
      refine ⟨e :: s, ?_, ?_⟩
      · simp only [sf667e, List.mem_flatMap, List.mem_map]
        exact ⟨e, hel, s, hs, rfl⟩
      · intro x hx
        simp only [List.toFinset_cons, Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact he
        · exact (Finset.mem_erase.mp (hsD hx)).2

def sf667q {α : Type} (c : α → α → Bool) (Q : List α → Bool) : ℕ → ℕ → List α → List α → Bool
  | _, 0, acc, _ => Q acc
  | 0, _ + 1, _, _ => true
  | _ + 1, _ + 1, _, [] => true
  | n + 1, k + 1, acc, t :: l => sf667q c Q n (k + 1) acc l && sf667q c Q n k (t :: acc) (l.filter (c t))

theorem sf667q_complete {α : Type} [DecidableEq α] (c : α → α → Bool) (Q : List α → Bool) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ (k : ℕ) (acc : List α) (S : Finset α),
      (∀ a ∈ S, a ∈ l) → (∀ a ∈ S, ∀ b ∈ S, a ≠ b → c a b = true) → S.card = k →
      sf667q c Q n k acc l = true → ∃ L : List α, (∀ a, a ∈ L ↔ a ∈ acc ∨ a ∈ S) ∧ Q L = true := by
  intro n
  induction n with
  | zero =>
    intro l hl k acc S hS _ hk hq
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst hl0
    have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
    subst hS0
    have hk0 : k = 0 := by simpa using hk.symm
    subst hk0
    exact ⟨acc, by simp, by simpa [sf667q] using hq⟩
  | succ n ih =>
    intro l hl k acc S hS hc hk hq
    cases k with
    | zero =>
      have hS0 : S = ∅ := Finset.card_eq_zero.mp hk
      subst hS0
      exact ⟨acc, by simp, by simpa [sf667q] using hq⟩
    | succ k =>
      match l, hl, hS, hq with
      | [], _, hS, _ =>
        have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
        subst hS0
        simp at hk
      | t :: l, hl, hS, hq =>
        rw [sf667q, Bool.and_eq_true] at hq
        by_cases ht : t ∈ S
        · have hsub : ∀ a ∈ S.erase t, a ∈ l.filter (c t) := by
            intro a ha
            have hne : a ≠ t := (Finset.mem_erase.mp ha).1
            have haS : a ∈ S := (Finset.mem_erase.mp ha).2
            have ha' : a ∈ t :: l := hS a haS
            have hal : a ∈ l := by
              rcases List.mem_cons.mp ha' with h | h
              · exact absurd h hne
              · exact h
            exact List.mem_filter.mpr ⟨hal, hc t ht a haS (Ne.symm hne)⟩
          have hlen : (l.filter (c t)).length ≤ n := by
            have := List.length_filter_le (c t) l
            simp only [List.length_cons] at hl
            omega
          have hcard : (S.erase t).card = k := by
            have := Finset.card_erase_add_one ht
            omega
          obtain ⟨L, hL, hQ⟩ := ih (l.filter (c t)) hlen k (t :: acc) (S.erase t) hsub
            (fun a ha b hb hab => hc a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2 hab)
            hcard hq.2
          refine ⟨L, ?_, hQ⟩
          intro a
          rw [hL, List.mem_cons, Finset.mem_erase]
          constructor
          · rintro ((rfl | h) | h)
            · exact Or.inr ht
            · exact Or.inl h
            · exact Or.inr h.2
          · rintro (h | h)
            · exact Or.inl (Or.inr h)
            · by_cases hat : a = t
              · exact Or.inl (Or.inl hat)
              · exact Or.inr ⟨hat, h⟩
        · have hlen : l.length ≤ n := by simpa using hl
          refine ih l hlen (k + 1) acc S ?_ hc hk hq.1
          intro a ha
          rcases List.mem_cons.mp (hS a ha) with h | h
          · exact absurd (h ▸ ha) ht
          · exact h

def sf667L : List (Finset (Fin 13)) :=
  [{0,1,2}, {3,4,5}, {6,7,8}, {2,7,9}, {1,4,9}, {5,8,9}, {2,8,10}, {4,7,10},
   {1,5,10}, {1,7,11}, {2,5,11}, {4,8,11}, {2,4,12}, {1,8,12}, {5,7,12},
   {0,9,10}, {3,9,12}, {6,9,11}]
def sf667F : Finset (Finset (Fin 13)) := sf667L.toFinset
def sf667P : Finset (Finset (Fin 13)) := {{0,1,2}, {3,4,5}, {6,7,8}}
def sf667W : List (Fin 13 × List ℕ) := [(0, [1, 3, 13]), (1, [1, 2, 15]), (2, [1, 2, 15]), (3, [0, 5, 7]), (4, [0, 2, 16]), (5, [0, 2, 16]), (6, [0, 5, 7]), (7, [0, 1, 17]), (8, [0, 1, 17]), (9, [0, 1, 2]), (10, [0, 1, 2]), (11, [0, 1, 2]), (12, [0, 1, 2])]

def sf667dc (s t : Finset (Fin 13)) : Bool := decide (Disjoint s t)


def sf667S : Finset (Fin 13) := sf667P.biUnion id
def sf667Ic : List ℕ := [46937, 89522, 158444, 251645, 244667, 257406, 48621, 56286, 59379, 159645, 155499, 147190, 97499, 97141, 96174, 229881, 258106, 233020]
def sf667Cb : List ℕ := [7, 56, 448, 644, 530, 800, 1284, 1168, 1058, 2178, 2084, 2320, 4116, 4354, 4256, 1537, 4616, 2624]
def sf667gt (i : ℕ) : Finset (Fin 13) := sf667L.getD i ∅
def sf667icb (i j : ℕ) : Bool := (sf667Ic.getD i 0).testBit j
def sf667cb (i : ℕ) : ℕ := sf667Cb.getD i 0
def sf667Qn (L : List ℕ) : Bool := (List.finRange 13).any fun x => L.all fun i => (sf667cb i).testBit x.val
def sf667F' : List (List (Fin 13)) :=
  sf667L.map fun t => (List.finRange 13).filter fun x => decide (x ∈ t ∧ x ∈ sf667S)

set_option maxRecDepth 100000 in
theorem sf667_nd : sf667L.Nodup := by decide +kernel
theorem sf667_a1 : sf667F.card = 18 := by
  show sf667L.toFinset.card = 18
  rw [List.toFinset_card_of_nodup sf667_nd]; rfl
set_option maxRecDepth 100000 in
theorem sf667_a2' : ∀ t ∈ sf667P, t ∈ sf667L := by decide +kernel
theorem sf667_a2 : sf667P ⊆ sf667F := fun t ht => List.mem_toFinset.mpr (sf667_a2' t ht)
theorem sf667_a3 : sf667P.card = 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sf667_a4' : ∀ t ∈ sf667L, t.card = 3 := by decide +kernel
theorem sf667_a4 : ∀ t ∈ sf667F, t.card = 3 := fun t ht => sf667_a4' t (List.mem_toFinset.mp ht)
set_option maxRecDepth 100000 in
theorem sf667_a6 : ∀ a ∈ sf667P, ∀ b ∈ sf667P, a ≠ b → Disjoint a b := by decide +kernel
set_option maxRecDepth 100000 in
theorem sf667_maxc : sf667c sf667dc sf667L.length sf667L = 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sf667_q : sf667q sf667icb sf667Qn 18 5 [] (List.range 18) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem sf667_h1 : ∀ i j : Fin 18, sf667icb i.val j.val = decide (¬ Disjoint (sf667gt i.val) (sf667gt j.val)) := by decide +kernel
set_option maxRecDepth 100000 in
theorem sf667_h2 : ∀ (i : Fin 18) (x : Fin 13), (sf667cb i.val).testBit x.val = decide (x ∈ sf667gt i.val) := by decide +kernel
set_option maxRecDepth 100000 in
theorem sf667_e0 : sf667e 6 sf667F' = [] := by decide +kernel
set_option maxRecDepth 100000 in
theorem sf667_w : ∀ q ∈ sf667W, q.2.Nodup ∧ q.2.length = 3 ∧ (∀ i ∈ q.2, i < 18 ∧ (sf667gt i).card = 3 ∧ q.1 ∉ sf667gt i) ∧
    ∀ i ∈ q.2, ∀ j ∈ q.2, i ≠ j → Disjoint (sf667gt i) (sf667gt j) := by decide +kernel
set_option maxRecDepth 100000 in
theorem sf667_g' : ∀ t ∈ sf667P,
    (((sf667L.filter (fun s => decide ((s ∩ sf667P.biUnion id).card = 1))).toFinset.biUnion id) ∩ t).card ≤ 1 := by decide +kernel
theorem sf667_g : ∀ t ∈ sf667P,
    (((sf667F.filter (fun s => (s ∩ sf667P.biUnion id).card = 1)).biUnion id) ∩ t).card ≤ 1 := by
  intro t ht
  have e : sf667F.filter (fun s => (s ∩ sf667P.biUnion id).card = 1)
      = (sf667L.filter (fun s => decide ((s ∩ sf667P.biUnion id).card = 1))).toFinset := by
    ext s
    simp [sf667F]
  rw [e]
  exact sf667_g' t ht

lemma sf667_idx (a : Finset (Fin 13)) (ha : a ∈ sf667L) : sf667L.idxOf a < 18 ∧ sf667gt (sf667L.idxOf a) = a := by
  have hlt : sf667L.idxOf a < sf667L.length := List.idxOf_lt_length_iff.mpr ha
  refine ⟨hlt, ?_⟩
  show sf667L.getD (sf667L.idxOf a) ∅ = a
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_idxOf hlt

set_option maxRecDepth 100000 in
theorem sf667_b5 : ∀ i j : Fin 18, i ≠ j → ∀ x : Fin 13, (sf667cb i.val).testBit x.val = true →
    (sf667cb j.val).testBit x.val = true → ∀ y : Fin 13, y ≠ x → (sf667cb i.val).testBit y.val = true →
    (sf667cb j.val).testBit y.val = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem sf667_bwc : ∀ (i : Fin 18) (x : Fin 13), (sf667cb i.val).testBit x.val = true → ∃ q ∈ sf667W, q.1 = x := by decide +kernel

set_option maxRecDepth 100000 in
theorem sf667_bcov : ∀ i : Fin 18, ∃ x ∈ ([1,2,4,7,9] : List (Fin 13)), (sf667cb i.val).testBit x.val = true := by decide +kernel

lemma sf667_bit (a : Finset (Fin 13)) (ha : a ∈ sf667L) (x : Fin 13) (hx : x ∈ a) :
    (sf667cb (sf667L.idxOf a)).testBit x.val = true := by
  obtain ⟨h1, h2⟩ := sf667_idx a ha
  have := sf667_h2 ⟨_, h1⟩ x
  simp only at this
  rw [this, h2]
  exact decide_eq_true hx

theorem sf667_a5 : ∀ a ∈ sf667F, ∀ b ∈ sf667F, a ≠ b → (a ∩ b).card ≤ 1 := by
  intro a ha b hb hab
  have ha' := List.mem_toFinset.mp ha
  have hb' := List.mem_toFinset.mp hb
  have ia := sf667_idx a ha'
  have ib := sf667_idx b hb'
  by_contra h
  have h2 : 1 < (a ∩ b).card := by omega
  obtain ⟨x, hx, y, hy, hne⟩ := Finset.one_lt_card.mp h2
  have hne' : (⟨_, ia.1⟩ : Fin 18) ≠ ⟨_, ib.1⟩ := by
    intro he
    apply hab
    rw [← ia.2, ← ib.2]
    exact congrArg sf667gt (Fin.mk.inj_iff.mp he)
  have := sf667_b5 _ _ hne' x (sf667_bit a ha' x (Finset.mem_inter.mp hx).1) (sf667_bit b hb' x (Finset.mem_inter.mp hx).2)
    y (Ne.symm hne) (sf667_bit a ha' y (Finset.mem_inter.mp hy).1)
  rw [sf667_bit b hb' y (Finset.mem_inter.mp hy).2] at this
  simp at this

theorem sf667_wc : ∀ x : Fin 13, x ∈ sf667F.biUnion id → ∃ q ∈ sf667W, q.1 = x := by
  intro x hx
  obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
  have ht' := List.mem_toFinset.mp ht
  exact sf667_bwc ⟨_, (sf667_idx t ht').1⟩ x (sf667_bit t ht' x hxt)

theorem sf667_cov : ∀ t ∈ sf667F, ¬ Disjoint ({1,2,4,7,9} : Finset (Fin 13)) t := by
  intro t ht
  have ht' := List.mem_toFinset.mp ht
  have ii := sf667_idx t ht'
  obtain ⟨x, hx, hbit⟩ := sf667_bcov ⟨_, ii.1⟩
  rw [Finset.not_disjoint_iff]
  refine ⟨x, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [hx]
  · have h2 := sf667_h2 ⟨_, ii.1⟩ x
    simp only at h2
    rw [hbit] at h2
    have := of_decide_eq_true h2.symm
    rw [ii.2] at this
    exact this

theorem finite_linear_stable_single_packing_forced_points_counterexample :
    ∃ (F P : Finset (Finset (Fin 13))),
      F.card = 18 ∧ P ⊆ F ∧ P.card = 3 ∧
      (∀ t ∈ F, t.card = 3) ∧
      (F : Set (Finset (Fin 13))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ∧
      (P : Set (Finset (Fin 13))).Pairwise Disjoint ∧
      (∀ Q : Finset (Finset (Fin 13)), Q ⊆ F →
        (Q : Set (Finset (Fin 13))).Pairwise Disjoint → Q.card ≤ 3) ∧
      (∀ x ∈ F.biUnion id, ∃ Q : Finset (Finset (Fin 13)),
        Q ⊆ F ∧ Q.card = 3 ∧ (Q : Set (Finset (Fin 13))).Pairwise Disjoint ∧
        x ∉ Q.biUnion id) ∧
      (∀ S : Finset (Finset (Fin 13)), S ⊆ F → S.card = 5 →
        (S : Set (Finset (Fin 13))).Pairwise (fun a b => ¬ Disjoint a b) →
        ∃ x : Fin 13, ∀ t ∈ S, x ∈ t) ∧
      (∀ t ∈ P,
        (((F.filter (fun s => (s ∩ P.biUnion id).card = 1)).biUnion id) ∩ t).card ≤ 1) ∧
      (∀ C : Finset (Fin 13), C ⊆ P.biUnion id → C.card ≤ 6 →
        ∃ t ∈ F, Disjoint C t) ∧
      ∃ C : Finset (Fin 13), C.card = 5 ∧ ∀ t ∈ F, ¬ Disjoint C t := by
  refine ⟨sf667F, sf667P, sf667_a1, sf667_a2, sf667_a3, sf667_a4,
    fun a ha b hb hab => sf667_a5 a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab,
    fun a ha b hb hab => sf667_a6 a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab,
    ?_, ?_, ?_, sf667_g, ?_, {1,2,4,7,9}, by decide +kernel, sf667_cov⟩
  · intro Q hsub hpw
    calc Q.card ≤ sf667c sf667dc sf667L.length sf667L :=
          sf667c_bound sf667dc _ sf667L le_rfl Q (fun a ha => List.mem_toFinset.mp (hsub ha))
            (fun a ha b hb hab => decide_eq_true (hpw (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab))
      _ = 3 := sf667_maxc
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := sf667_wc x hx
    obtain ⟨hnd, hlen, h2, h3⟩ := sf667_w q hq
    have hgtmem : ∀ i, i < 18 → sf667gt i ∈ sf667L := by
      intro i hi
      have hlt : i < sf667L.length := hi
      have : sf667L.getD i ∅ = sf667L[i] := by
        rw [List.getD_eq_getElem _ _ hlt]
      show sf667L.getD i ∅ ∈ sf667L
      rw [this]
      exact List.getElem_mem hlt
    have hinj : (q.2.map sf667gt).Nodup := by
      refine List.Nodup.map_on ?_ hnd
      intro i hi j hj hij
      by_contra hne
      have hdis := h3 i hi j hj hne
      rw [hij, disjoint_self] at hdis
      have hc := (h2 j hj).2.1
      simp only [Finset.bot_eq_empty] at hdis
      rw [hdis] at hc
      simp at hc
    refine ⟨(q.2.map sf667gt).toFinset, ?_, ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      exact List.mem_toFinset.mpr (hgtmem i (h2 i hi).1)
    · rw [List.toFinset_card_of_nodup hinj, List.length_map, hlen]
    · intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_coe.mp ha))
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_coe.mp hb))
      exact h3 i hi j hj (fun h => hab (by rw [h]))
    · simp only [Finset.mem_biUnion, id]
      rintro ⟨t, ht, hxt⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      exact (h2 i hi).2.2 hxt
  · intro S hsub hcard hpw
    let idx : Finset (Fin 13) → ℕ := fun a => sf667L.idxOf a
    have hidx : ∀ a ∈ S, idx a < 18 ∧ sf667gt (idx a) = a := by
      intro a ha
      have haL : a ∈ sf667L := List.mem_toFinset.mp (hsub ha)
      have hlt : idx a < sf667L.length := List.idxOf_lt_length_iff.mpr haL
      refine ⟨hlt, ?_⟩
      show sf667L.getD (sf667L.idxOf a) ∅ = a
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_idxOf hlt
    have hinj : Set.InjOn idx (S : Set (Finset (Fin 13))) := by
      intro a ha b hb hab
      have h1 := (hidx a (Finset.mem_coe.mp ha)).2
      have h2 := (hidx b (Finset.mem_coe.mp hb)).2
      rw [← h1, ← h2, hab]
    obtain ⟨L, hL, hQ⟩ := sf667q_complete sf667icb sf667Qn 18 (List.range 18) (by simp) 5 [] (S.image idx)
      (fun i hi => by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
        exact List.mem_range.mpr (hidx a ha).1)
      (fun i hi j hj hij => by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
        have hab : a ≠ b := fun h => hij (by rw [h])
        have hia := hidx a ha
        have hib := hidx b hb
        have := sf667_h1 ⟨idx a, hia.1⟩ ⟨idx b, hib.1⟩
        simp only at this
        rw [this, hia.2, hib.2]
        exact decide_eq_true (hpw (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab))
      (by rw [Finset.card_image_of_injOn hinj, hcard]) sf667_q
    obtain ⟨x, _, hx⟩ := List.any_eq_true.mp hQ
    refine ⟨x, fun t ht => ?_⟩
    have ht' := hidx t ht
    have hmem : idx t ∈ L := (hL _).mpr (Or.inr (Finset.mem_image_of_mem _ ht))
    have hbit := List.all_eq_true.mp hx _ hmem
    have h2 := sf667_h2 ⟨idx t, ht'.1⟩ x
    simp only at h2
    rw [hbit] at h2
    have := of_decide_eq_true h2.symm
    rw [ht'.2] at this
    exact this
  · intro C hsub hcard
    by_contra h
    push Not at h
    have hhit : ∀ l ∈ sf667F', ∃ e ∈ C, e ∈ l := by
      intro l hl
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
      obtain ⟨x, hxC, hxt⟩ := Finset.not_disjoint_iff.mp (h t (List.mem_toFinset.mpr ht))
      refine ⟨x, hxC, List.mem_filter.mpr ⟨List.mem_finRange x, decide_eq_true ⟨hxt, hsub hxC⟩⟩⟩
    obtain ⟨s, hs, _⟩ := sf667e_complete 6 sf667F' C hhit hcard
    rw [sf667_e0] at hs
    simp at hs
