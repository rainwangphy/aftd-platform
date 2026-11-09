import AFTD.Prelude

/-!
# finite_binary_stable_single_packing_forced_points_counterexample

Topic: graphs   Node: 7cfc47376f44

Provenance: helper lemma. Explicit rank-five binary geometry and independently checked enumeration in experiments 16124 and 16128. The relation to Fano-free binary geometries is discussed at https://ris.utwente.nl/ws/portalfiles/portal/421363158/22m1511229.pdf.

A stable binary three-point-line system can have a maximum packing P of five lines with at most one singly forced point per P-line, while no cover of size ten is contained in P. The example has a Fano-plane restriction.
-/

abbrev In668Tri := ℕ × ℕ × ℕ

def in668F32 (x : ℕ) : Fin 32 := Fin.ofNat 32 x

def in668enc (t : In668Tri) : Finset (Fin 32) := {in668F32 t.1, in668F32 t.2.1, in668F32 t.2.2}

def in668dj (t s : In668Tri) : Bool :=
  (t.1 % 32 != s.1 % 32) && (t.1 % 32 != s.2.1 % 32) && (t.1 % 32 != s.2.2 % 32) &&
  (t.2.1 % 32 != s.1 % 32) && (t.2.1 % 32 != s.2.1 % 32) && (t.2.1 % 32 != s.2.2 % 32) &&
  (t.2.2 % 32 != s.1 % 32) && (t.2.2 % 32 != s.2.1 % 32) && (t.2.2 % 32 != s.2.2 % 32)

def in668L : List In668Tri := [(1,6,7),(1,8,9),(1,12,13),(1,22,23),(1,28,29),(1,30,31),(3,9,10),(3,12,15),(3,21,22),(3,24,27),(3,28,31),(3,29,30),(6,9,15),(6,10,12),(6,17,23),(6,24,30),(6,27,29),(7,8,15),(7,10,13),(7,17,22),(7,24,31),(7,27,28),(8,21,29),(8,22,30),(8,23,31),(9,17,24),(9,21,28),(9,22,31),(9,23,30),(10,17,27),(10,21,31),(10,22,28),(10,23,29),(12,17,29),(12,23,27),(13,17,28),(13,21,24),(13,22,27),(15,17,30),(15,23,24)]
def in668PL : List In668Tri := [(1,30,31),(3,9,10),(7,27,28),(12,17,29),(15,23,24)]

def in668dfs : ℕ → List In668Tri → List In668Tri → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | k + 1, ch, t :: l =>
    (!(ch.all (fun c => in668dj c t)) || in668dfs k (t :: ch) l) && in668dfs (k + 1) ch l

def in668UL : List ℕ := [1, 3, 7, 9, 10, 12, 15, 17, 23, 24, 27, 28, 29, 30, 31]

def in668TR : List (List ℕ) := in668L.map (fun t => [t.1, t.2.1, t.2.2].filter (fun x => in668UL.contains x))

def in668nh : ℕ → List ℕ → Bool
  | 0, acc => (in668TR.find? (fun r => r.all (fun y => !acc.contains y))).isSome
  | k + 1, acc =>
    match in668TR.find? (fun r => r.all (fun y => !acc.contains y)) with
    | none => false
    | some r => r.all (fun x => in668nh k (x :: acc))

def in668W : ℕ → List In668Tri
  | 1 => [(3,9,10),(6,17,23),(7,24,31),(8,21,29),(13,22,27)]
  | 3 => [(1,6,7),(8,21,29),(9,17,24),(10,22,28),(12,23,27)]
  | 6 => [(1,8,9),(3,12,15),(7,17,22),(10,23,29),(13,21,24)]
  | 7 => [(1,8,9),(3,12,15),(6,17,23),(10,21,31),(13,22,27)]
  | 8 => [(1,6,7),(3,9,10),(12,17,29),(13,22,27),(15,23,24)]
  | 9 => [(1,6,7),(3,12,15),(8,22,30),(10,17,27),(13,21,24)]
  | 10 => [(1,6,7),(3,12,15),(8,21,29),(9,17,24),(13,22,27)]
  | 12 => [(1,6,7),(3,9,10),(8,21,29),(13,17,28),(15,23,24)]
  | 13 => [(1,6,7),(3,9,10),(8,21,29),(12,23,27),(15,17,30)]
  | 15 => [(1,6,7),(3,9,10),(8,21,29),(12,23,27),(13,17,28)]
  | 17 => [(1,6,7),(3,9,10),(8,21,29),(13,22,27),(15,23,24)]
  | 21 => [(1,6,7),(3,9,10),(8,22,30),(12,17,29),(15,23,24)]
  | 22 => [(1,6,7),(3,9,10),(8,21,29),(12,23,27),(13,17,28)]
  | 23 => [(1,6,7),(3,9,10),(8,21,29),(13,22,27),(15,17,30)]
  | 24 => [(1,6,7),(3,9,10),(8,21,29),(12,23,27),(13,17,28)]
  | 27 => [(1,6,7),(3,9,10),(8,21,29),(13,17,28),(15,23,24)]
  | 28 => [(1,6,7),(3,9,10),(8,21,29),(12,23,27),(15,17,30)]
  | 29 => [(1,6,7),(3,9,10),(8,22,30),(12,23,27),(13,17,28)]
  | 30 => [(1,6,7),(3,9,10),(8,21,29),(12,23,27),(13,17,28)]
  | 31 => [(1,6,7),(3,9,10),(8,21,29),(12,23,27),(13,17,28)]
  | _ => []

def in668S : Finset (Fin 32) := {1,3,6,7,8,9,10,12,13,15,17,21,22,23,24,27,28,29,30,31}
def in668Fs : Finset (Finset (Fin 32)) := (in668L.map in668enc).toFinset
def in668P : Finset (Finset (Fin 32)) := (in668PL.map in668enc).toFinset

theorem in668_dfs_spec : ∀ (k : ℕ) (L ch : List In668Tri),
    in668dfs k ch L = true → ∀ Q : List In668Tri, Q.Sublist L →
    (∀ s ∈ Q, ch.all (fun c => in668dj c s) = true) →
    Q.Pairwise (fun a b => in668dj a b = true) → Q.length < k := by
  intro k
  induction k with
  | zero =>
    intro L ch h
    cases L <;> simp [in668dfs] at h
  | succ k ih =>
    intro L
    induction L with
    | nil =>
      intro ch _ Q hQ _ _
      simp only [List.sublist_nil] at hQ
      subst hQ
      simp
    | cons t l ihl =>
      intro ch h Q hQ hch hpair
      simp only [in668dfs, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      obtain ⟨h1, h2⟩ := h
      cases hQ with
      | cons _ hQ' => exact ihl ch h2 Q hQ' hch hpair
      | cons_cons _ hQ' =>
        rename_i Q'
        have hpt : ∀ s ∈ Q', in668dj t s = true := fun s hs =>
          (List.pairwise_cons.1 hpair).1 s hs
        have hall : ch.all (fun c => in668dj c t) = true := hch t List.mem_cons_self
        have h1' : in668dfs k (t :: ch) l = true := by
          rcases h1 with h1 | h1
          · rw [h1] at hall
            exact absurd hall (by simp)
          · exact h1
        have := ih l (t :: ch) h1' Q' hQ' (fun s hs => by
          have h3 := hch s (List.mem_cons_of_mem _ hs)
          simp only [List.all_cons, hpt s hs, Bool.true_and]
          exact h3) (List.pairwise_cons.1 hpair).2
        simpa using this

theorem in668_nh_spec (C : Finset ℕ) (hhit : ∀ r ∈ in668TR, ∃ x ∈ r, x ∈ C) :
    ∀ (k : ℕ) (acc : List ℕ), in668nh k acc = true → acc.Nodup → (∀ x ∈ acc, x ∈ C) →
      ¬ C.card ≤ acc.length + k := by
  have key : ∀ (acc : List ℕ) (r : List ℕ),
      in668TR.find? (fun r => r.all (fun y => !acc.contains y)) = some r →
      ∃ x ∈ r, x ∈ C ∧ x ∉ acc := by
    intro acc r hr
    have hmem := List.mem_of_find?_eq_some hr
    have hp := List.find?_some hr
    obtain ⟨x, hx, hxC⟩ := hhit r hmem
    refine ⟨x, hx, hxC, ?_⟩
    have := List.all_eq_true.1 hp x hx
    simpa using this
  intro k
  induction k with
  | zero =>
    intro acc h hnd hsub hcard
    simp only [in668nh, Option.isSome_iff_exists] at h
    obtain ⟨r, hr⟩ := h
    obtain ⟨x, -, hxC, hxa⟩ := key acc r hr
    have hss : acc.toFinset ⊂ C := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨fun y hy => hsub y (List.mem_toFinset.1 hy), ?_⟩
      intro he
      exact hxa (List.mem_toFinset.1 (he ▸ hxC))
    have := Finset.card_lt_card hss
    rw [List.toFinset_card_of_nodup hnd] at this
    omega
  | succ k ih =>
    intro acc h hnd hsub hcard
    rw [in668nh] at h
    split at h
    · exact absurd h (by simp)
    · rename_i r hr
      obtain ⟨x, hx, hxC, hxa⟩ := key acc r hr
      have hk := List.all_eq_true.1 h x hx
      have := ih (x :: acc) hk (List.nodup_cons.2 ⟨hxa, hnd⟩)
        (by
          intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hxC
          · exact hsub y hy)
      apply this
      simp only [List.length_cons]
      omega

theorem in668_dj_of_disjoint (a b : In668Tri) (h : Disjoint (in668enc a) (in668enc b)) :
    in668dj a b = true := by
  have H := Finset.disjoint_left.1 h
  have key : ∀ u v, in668F32 u ∈ in668enc a → in668F32 v ∈ in668enc b → u % 32 ≠ v % 32 := by
    intro u v hu hv heq
    have he : in668F32 u = in668F32 v := Fin.ext (by simpa [in668F32, Fin.ofNat] using heq)
    exact H hu (he ▸ hv)
  simp only [in668dj, Bool.and_eq_true, bne_iff_ne]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
    exact key _ _ (by simp [in668enc]) (by simp [in668enc])


def in668pw : List In668Tri → Bool
  | [] => true
  | t :: l => l.all (in668dj t) && in668pw l

def in668DL : List ℕ := [3,8,13,21,22,24,27,29,30]

theorem in668_F32_val (x : ℕ) : (in668F32 x).val = x % 32 := rfl

theorem in668_disjoint_of_dj (a b : In668Tri) (h : in668dj a b = true) :
    Disjoint (in668enc a) (in668enc b) := by
  simp only [in668dj, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine Finset.disjoint_left.2 fun y hya hyb => ?_
  simp only [in668enc, Finset.mem_insert, Finset.mem_singleton] at hya hyb
  have key : ∀ u v, y = in668F32 u → y = in668F32 v → u % 32 = v % 32 := by
    intro u v e1 e2
    have := congrArg Fin.val (e1.symm.trans e2)
    simpa only [in668_F32_val] using this
  rcases hya with e | e | e <;> rcases hyb with e' | e' | e'
  · exact h1 (key _ _ e e')
  · exact h2 (key _ _ e e')
  · exact h3 (key _ _ e e')
  · exact h4 (key _ _ e e')
  · exact h5 (key _ _ e e')
  · exact h6 (key _ _ e e')
  · exact h7 (key _ _ e e')
  · exact h8 (key _ _ e e')
  · exact h9 (key _ _ e e')

theorem in668_enc_ne_empty (a : In668Tri) : in668enc a ≠ ∅ := by
  intro h
  have : in668F32 a.1 ∈ in668enc a := by simp [in668enc]
  rw [h] at this
  simp at this

theorem in668_pw_nodup : ∀ l : List In668Tri, in668pw l = true → (l.map in668enc).Nodup := by
  intro l
  induction l with
  | nil => simp
  | cons t l ih =>
    intro h
    simp only [in668pw, Bool.and_eq_true] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun b hb he => ?_, ih h.2⟩
    have hd := in668_disjoint_of_dj t b (List.all_eq_true.1 h.1 b hb)
    rw [he] at hd
    exact in668_enc_ne_empty t (Finset.disjoint_self_iff_empty _ |>.1 hd)

theorem in668_pw_disjoint : ∀ l : List In668Tri, in668pw l = true →
    ∀ a ∈ l, ∀ b ∈ l, in668enc a ≠ in668enc b → Disjoint (in668enc a) (in668enc b) := by
  intro l
  induction l with
  | nil => simp
  | cons t l ih =>
    intro h a ha b hb hne
    simp only [in668pw, Bool.and_eq_true] at h
    have hall := List.all_eq_true.1 h.1
    rcases List.mem_cons.1 ha with e | ha' <;> rcases List.mem_cons.1 hb with e' | hb'
    · subst e; subst e'; exact absurd rfl hne
    · subst e; exact in668_disjoint_of_dj _ _ (hall b hb')
    · subst e'; exact (in668_disjoint_of_dj _ _ (hall a ha')).symm
    · exact ih h.2 a ha' b hb' hne

theorem in668_pw_toFinset (l : List In668Tri) (h : in668pw l = true) :
    ((l.map in668enc).toFinset.card = l.length) ∧
    ∀ s ∈ (l.map in668enc).toFinset, ∀ t ∈ (l.map in668enc).toFinset, s ≠ t → Disjoint s t := by
  refine ⟨?_, ?_⟩
  · rw [List.toFinset_card_of_nodup (in668_pw_nodup l h), List.length_map]
  · intro s hs t ht hst
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ht)
    exact in668_pw_disjoint l h a ha b hb hst

theorem in668_pc7 : in668pw in668PL = true := by decide +kernel
theorem in668_c9 : ∀ x ∈ in668S,
    (in668W x.val).length = 5 ∧ in668pw (in668W x.val) = true ∧
    (in668W x.val).all (fun t => in668L.contains t) = true ∧
    (in668W x.val).all (fun t => (x.val != t.1 % 32) && (x.val != t.2.1 % 32) &&
      (x.val != t.2.2 % 32)) = true := by decide +kernel
theorem in668_Dp : ∀ y : Fin 32, y ∈ ({3,8,13,21,22,24,27,29,30} : Finset (Fin 32)) → in668DL.contains y.val = true := by
  decide +kernel
theorem in668_c10b : ∀ t ∈ in668PL, ∀ y ∈ [t.1 % 32, t.2.1 % 32, t.2.2 % 32],
    ∀ z ∈ [t.1 % 32, t.2.1 % 32, t.2.2 % 32], in668DL.contains y = true →
    in668DL.contains z = true → y = z := by decide +kernel

theorem in668_map_nodup : (in668L.map in668enc).Nodup := by decide +kernel
theorem in668_no6 : in668dfs 6 [] in668L = true := by decide +kernel
theorem in668_nh10 : in668nh 10 [] = true := by decide +kernel
theorem in668_L_lt : ∀ t ∈ in668L, t.1 < 32 ∧ t.2.1 < 32 ∧ t.2.2 < 32 := by decide +kernel
theorem in668_pts : ∀ x : Fin 32, x ∈ in668P.biUnion id → in668UL.contains x.val = true := by
  decide +kernel
theorem in668_bU_S : ∀ x ∈ in668Fs.biUnion id, x ∈ in668S := by decide +kernel
theorem in668_c5 : ∀ t ∈ in668L,
    in668F32 t.1 ∈ in668S ∧ in668F32 t.2.1 ∈ in668S ∧ in668F32 t.2.2 ∈ in668S ∧
    in668F32 t.1 ≠ in668F32 t.2.1 ∧ in668F32 t.1 ≠ in668F32 t.2.2 ∧ in668F32 t.2.1 ≠ in668F32 t.2.2 ∧
    Nat.xor (in668F32 t.1).val (in668F32 t.2.1).val = (in668F32 t.2.2).val := by decide +kernel
theorem in668_c10a : ∀ t ∈ in668L, ((in668enc t ∩ in668P.biUnion id).card = 1 →
    in668enc t ⊆ ({3,8,13,21,22,24,27,29,30} : Finset (Fin 32))) := by decide +kernel
theorem in668_c6 : ∀ a ∈ in668S, ∀ b ∈ in668S, ∀ c ∈ in668S, a ≠ b → a ≠ c → b ≠ c →
    Nat.xor a.val b.val = c.val → ({a, b, c} : Finset (Fin 32)) ∈ in668Fs := by decide +kernel

theorem finite_binary_stable_single_packing_forced_points_counterexample :
    ∃ (S : Finset (Fin 32)) (F P : Finset (Finset (Fin 32))),
      S.card = 20 ∧ F.card = 40 ∧ P ⊆ F ∧ P.card = 5 ∧
      (∀ t ∈ F, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ t = {a,b,c} ∧ Nat.xor a.val b.val = c.val) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
        Nat.xor a.val b.val = c.val → ({a,b,c} : Finset (Fin 32)) ∈ F) ∧
      (P : Set (Finset (Fin 32))).Pairwise Disjoint ∧
      (∀ Q : Finset (Finset (Fin 32)), Q ⊆ F →
        (Q : Set (Finset (Fin 32))).Pairwise Disjoint → Q.card ≤ 5) ∧
      (∀ x ∈ F.biUnion id, ∃ Q : Finset (Finset (Fin 32)),
        Q ⊆ F ∧ Q.card = 5 ∧ (Q : Set (Finset (Fin 32))).Pairwise Disjoint ∧
        x ∉ Q.biUnion id) ∧
      (∀ t ∈ P,
        (((F.filter (fun s => (s ∩ P.biUnion id).card = 1)).biUnion id) ∩ t).card ≤ 1) ∧
      (∀ C : Finset (Fin 32), C ⊆ P.biUnion id → C.card ≤ 10 →
        ∃ t ∈ F, Disjoint C t) ∧
      ({3,9,10,21,22,28,31} : Finset (Fin 32)) ⊆ S := by
  refine ⟨in668S, in668Fs, in668P, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_, in668_c6, ?_, ?_, ?_, ?_, ?_, by decide +kernel⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ht)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := in668_c5 u hu
    exact ⟨_, h1, _, h2, _, h3, h4, h5, h6, rfl, h7⟩
  · intro s hs t ht hst
    exact (in668_pw_toFinset in668PL in668_pc7).2 s hs t ht hst
  · intro Q hQ hpair
    classical
    let Q' := in668L.filter (fun t => decide (in668enc t ∈ Q))
    have hsub : Q'.Sublist in668L := List.filter_sublist
    have hcard : Q.card ≤ Q'.length := by
      have hle : Q ⊆ (Q'.map in668enc).toFinset := by
        intro s hs
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 (hQ hs))
        exact List.mem_toFinset.2 (List.mem_map.2 ⟨u, List.mem_filter.2 ⟨hu, by simpa using hs⟩, rfl⟩)
      have h1 := Finset.card_le_card hle
      have h2 := List.toFinset_card_le (Q'.map in668enc)
      simp only [List.length_map] at h2
      omega
    have hne : Q'.Pairwise (fun a b => in668enc a ≠ in668enc b) :=
      (List.pairwise_map.1 in668_map_nodup).sublist hsub
    have hdj : Q'.Pairwise (fun a b => in668dj a b = true) := by
      refine hne.imp_of_mem ?_
      intro a b ha hb hab
      have ha' := of_decide_eq_true (List.mem_filter.1 ha).2
      have hb' := of_decide_eq_true (List.mem_filter.1 hb).2
      exact in668_dj_of_disjoint a b (hpair ha' hb' hab)
    have := in668_dfs_spec 6 in668L [] in668_no6 Q' hsub (by simp) hdj
    omega
  · intro x hx
    have hxS := in668_bU_S x hx
    obtain ⟨h1, h2, h3, h4⟩ := in668_c9 x hxS
    obtain ⟨hc, hd⟩ := in668_pw_toFinset _ h2
    refine ⟨((in668W x.val).map in668enc).toFinset, ?_, by rw [hc, h1], fun s hs t ht hst => hd s hs t ht hst, ?_⟩
    · intro s hs
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs)
      have := List.all_eq_true.1 h3 u hu
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨u, by simpa using this, rfl⟩)
    · intro hmem
      obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.1 hmem
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs)
      have hk := List.all_eq_true.1 h4 u hu
      simp only [Bool.and_eq_true, bne_iff_ne] at hk
      simp only [in668enc, Finset.mem_insert, Finset.mem_singleton, id] at hxs
      rcases hxs with e | e | e
      · exact hk.1.1 (by rw [e, in668_F32_val])
      · exact hk.1.2 (by rw [e, in668_F32_val])
      · exact hk.2 (by rw [e, in668_F32_val])
  · intro t ht
    have hD : ∀ y ∈ (in668Fs.filter (fun s => (s ∩ in668P.biUnion id).card = 1)).biUnion id,
        in668DL.contains y.val = true := by
      intro y hy
      obtain ⟨s, hs, hys⟩ := Finset.mem_biUnion.1 hy
      obtain ⟨hsF, hsc⟩ := Finset.mem_filter.1 hs
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hsF)
      exact in668_Dp y (in668_c10a u hu hsc hys)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ht)
    refine Finset.card_le_one.2 fun y hy z hz => ?_
    obtain ⟨hy1, hy2⟩ := Finset.mem_inter.1 hy
    obtain ⟨hz1, hz2⟩ := Finset.mem_inter.1 hz
    have hval : ∀ w ∈ in668enc p, w.val ∈ [p.1 % 32, p.2.1 % 32, p.2.2 % 32] := by
      intro w hw
      simp only [in668enc, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> simp [in668_F32_val]
    exact Fin.ext (in668_c10b p hp _ (hval y hy2) _ (hval z hz2) (hD y hy1) (hD z hz1))
  · intro C hC hcard
    classical
    by_contra hcon
    push Not at hcon
    have hhit : ∀ r ∈ in668TR, ∃ x ∈ r, x ∈ C.image Fin.val := by
      intro r hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
      have huF : in668enc u ∈ in668Fs := List.mem_toFinset.2 (List.mem_map.2 ⟨u, hu, rfl⟩)
      obtain ⟨y, hyC, hyu⟩ := Finset.not_disjoint_iff.1 (hcon _ huF)
      obtain ⟨h1, h2, h3⟩ := in668_L_lt u hu
      have hyU := in668_pts y (hC hyC)
      have hval : y.val ∈ [u.1, u.2.1, u.2.2] := by
        simp only [in668enc, Finset.mem_insert, Finset.mem_singleton] at hyu
        rcases hyu with rfl | rfl | rfl
        · simp only [in668F32, Fin.ofNat, Nat.mod_eq_of_lt h1]
          simp
        · simp only [in668F32, Fin.ofNat, Nat.mod_eq_of_lt h2]
          simp
        · simp only [in668F32, Fin.ofNat, Nat.mod_eq_of_lt h3]
          simp
      exact ⟨y.val, List.mem_filter.2 ⟨hval, hyU⟩, Finset.mem_image_of_mem _ hyC⟩
    have := in668_nh_spec (C.image Fin.val) hhit 10 [] in668_nh10 List.nodup_nil (by simp)
    apply this
    rw [Finset.card_image_of_injective _ Fin.val_injective]
    simp only [List.length_nil]
    omega
