import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_maximal_packing_single_forced_edge_support_counterexample

Topic: graphs   Node: da59eb349415

Provenance: helper lemma. Explicit two-five-cycle construction verified in experiment 16162.

A graph has a maximal edge-disjoint packing P of five triangles with at most one singly forced edge on each packed triangle, but no ten-edge triangle cover supported by P. The graph has nine edge-disjoint triangles, so P is not maximum.
-/

abbrev In670Tri := ℕ × ℕ × ℕ

def in670F (x : ℕ) : Fin 16 := Fin.ofNat 16 x

def in670ec (x y : ℕ) : ℕ := if x < y then x * 16 + y else y * 16 + x

def in670eL : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 18, 21, 22, 27, 35, 39, 44, 52, 56, 61, 69, 73, 78, 90, 95, 103, 106, 107, 120, 124, 137, 141, 154, 158, 175]

def in670G : SimpleGraph (Fin 16) :=
  SimpleGraph.fromRel (fun a b : Fin 16 => in670eL.contains (in670ec a.val b.val) = true)

def in670adjB (a b : Fin 16) : Bool := (a.val != b.val) && in670eL.contains (in670ec a.val b.val)

def in670tc (t : In670Tri) : List ℕ :=
  [in670ec (t.1 % 16) (t.2.1 % 16), in670ec (t.1 % 16) (t.2.2 % 16), in670ec (t.2.1 % 16) (t.2.2 % 16)]

def in670e3 (t : In670Tri) : Finset (Fin 16) := {in670F t.1, in670F t.2.1, in670F t.2.2}

def in670PL : List In670Tri := [(0,1,6),(0,2,7),(0,3,8),(0,4,9),(0,5,10)]
def in670QL : List In670Tri := [(0,1,2),(0,3,4),(0,5,10),(0,6,7),(0,8,9),(1,6,11),(2,7,12),(3,8,13),(4,9,14)]
def in670TL : List In670Tri := [(0,1,2),(0,1,5),(0,1,6),(0,2,3),(0,2,7),(0,3,4),(0,3,8),(0,4,5),(0,4,9),(0,5,10),(0,6,7),(0,6,10),(0,7,8),(0,8,9),(0,9,10),(1,6,11),(2,7,12),(3,8,13),(4,9,14),(5,10,15)]
def in670FC : List ℕ := [22, 39, 56, 73, 90]

def in670UC : List ℕ := in670PL.flatMap in670tc
def in670TR : List (List ℕ) := in670TL.map (fun t => (in670tc t).filter (fun x => in670UC.contains x))

def in670nh : ℕ → List ℕ → Bool
  | 0, acc => (in670TR.find? (fun r => r.all (fun y => !acc.contains y))).isSome
  | k + 1, acc =>
    match in670TR.find? (fun r => r.all (fun y => !acc.contains y)) with
    | none => false
    | some r => r.all (fun x => in670nh k (x :: acc))

theorem in670_nh_spec (C : Finset ℕ) (hhit : ∀ r ∈ in670TR, ∃ x ∈ r, x ∈ C) :
    ∀ (k : ℕ) (acc : List ℕ), in670nh k acc = true → acc.Nodup → (∀ x ∈ acc, x ∈ C) →
      ¬ C.card ≤ acc.length + k := by
  have key : ∀ (acc : List ℕ) (r : List ℕ),
      in670TR.find? (fun r => r.all (fun y => !acc.contains y)) = some r →
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
    simp only [in670nh, Option.isSome_iff_exists] at h
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
    rw [in670nh] at h
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

def in670sc : Sym2 (Fin 16) → ℕ :=
  Sym2.lift ⟨fun x y => in670ec x.val y.val, fun x y => by
    show in670ec x.val y.val = in670ec y.val x.val
    unfold in670ec; split_ifs <;> omega⟩

theorem in670_ec_inj (x y u v : Fin 16) (h : in670ec x.val y.val = in670ec u.val v.val) :
    s(x, y) = s(u, v) := by
  have hx := x.isLt; have hy := y.isLt; have hu := u.isLt; have hv := v.isLt
  unfold in670ec at h
  rw [Sym2.eq_iff]
  split_ifs at h with h1 h2 h2
  · left; constructor <;> (apply Fin.ext; omega)
  · right; constructor <;> (apply Fin.ext; omega)
  · right; constructor <;> (apply Fin.ext; omega)
  · left; constructor <;> (apply Fin.ext; omega)

theorem in670_sc_inj : Function.Injective in670sc := by
  intro e f
  induction e using Sym2.ind with
  | h x y =>
    induction f using Sym2.ind with
    | h u v => exact in670_ec_inj x y u v

theorem in670_enc3_fin (a b c : Fin 16) (e : Sym2 (Fin 16))
    (he : e ∈ finite_vertex_set_edge_encoding ({a, b, c} : Finset (Fin 16))) :
    in670sc e ∈ [in670ec a.val b.val, in670ec a.val c.val, in670ec b.val c.val] := by
  induction e using Sym2.ind with
  | h u v =>
    simp only [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mk_mem_sym2_iff,
      Finset.mem_insert, Finset.mem_singleton, Sym2.mk_isDiag_iff] at he
    obtain ⟨⟨hu, hv⟩, huv⟩ := he
    have hsym : ∀ p q : Fin 16, in670ec p.val q.val = in670ec q.val p.val := by
      intro p q; unfold in670ec; split_ifs <;> omega
    show in670ec u.val v.val ∈ [in670ec a.val b.val, in670ec a.val c.val, in670ec b.val c.val]
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      first | exact absurd rfl huv | simp [hsym]

theorem in670_enc3_codes (t : In670Tri) (e : Sym2 (Fin 16))
    (he : e ∈ finite_vertex_set_edge_encoding (in670e3 t)) : in670sc e ∈ in670tc t := by
  have := in670_enc3_fin _ _ _ e he
  simpa only [in670F, Fin.ofNat, in670tc] using this

theorem in670_mem_enc (s : Finset (Fin 16)) (x y : Fin 16) (hx : x ∈ s) (hy : y ∈ s) (h : x ≠ y) :
    s(x, y) ∈ finite_vertex_set_edge_encoding s := by
  simp only [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mk_mem_sym2_iff,
    Sym2.mk_isDiag_iff]
  exact ⟨⟨hx, hy⟩, h⟩

theorem in670_adj_iff (a b : Fin 16) : in670G.Adj a b ↔ in670adjB a b = true := by
  have hs : in670ec b.val a.val = in670ec a.val b.val := by unfold in670ec; split_ifs <;> omega
  simp only [in670G, SimpleGraph.fromRel_adj, in670adjB, Bool.and_eq_true, bne_iff_ne, hs,
    or_self, ne_eq, Fin.val_eq_val]

theorem in670_card_inter (t s : In670Tri) (hd : ∀ c ∈ in670tc t, c ∉ in670tc s) :
    (in670e3 t ∩ in670e3 s).card ≤ 1 := by
  refine Finset.card_le_one.2 fun x hx y hy => ?_
  by_contra hxy
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
  obtain ⟨hy1, hy2⟩ := Finset.mem_inter.1 hy
  have h1 := in670_enc3_codes t _ (in670_mem_enc _ x y hx1 hy1 hxy)
  have h2 := in670_enc3_codes s _ (in670_mem_enc _ x y hx2 hy2 hxy)
  exact hd _ h1 h2

theorem in670_nh10 : in670nh 10 [] = true := by decide +kernel
theorem in670_TL_adj : ∀ t ∈ in670TL, in670adjB (in670F t.1) (in670F t.2.1) = true ∧ in670adjB (in670F t.1) (in670F t.2.2) = true ∧
    in670adjB (in670F t.2.1) (in670F t.2.2) = true := by decide +kernel
theorem in670_P_sub : ∀ t ∈ in670PL, t ∈ in670TL := by decide +kernel
theorem in670_Q_sub : ∀ t ∈ in670QL, t ∈ in670TL := by decide +kernel
theorem in670_P_nodup : (in670PL.map in670e3).Nodup := by decide +kernel
theorem in670_Q_nodup : (in670QL.map in670e3).Nodup := by decide +kernel
theorem in670_P_len : in670PL.length = 5 := by decide +kernel
theorem in670_Q_len : in670QL.length = 9 := by decide +kernel
theorem in670_P_pw : ∀ t ∈ in670PL, ∀ s ∈ in670PL, t ≠ s → ∀ c ∈ in670tc t, c ∉ in670tc s := by
  decide +kernel
theorem in670_Q_pw : ∀ t ∈ in670QL, ∀ s ∈ in670QL, t ≠ s → ∀ c ∈ in670tc t, c ∉ in670tc s := by
  decide +kernel
theorem in670_c4 : ∀ a b : Fin 16, in670adjB a b = true → ∀ c : Fin 16, in670adjB a c = true →
    in670adjB b c = true →
    (in670UC.contains (in670ec a.val b.val) || in670UC.contains (in670ec a.val c.val) ||
      in670UC.contains (in670ec b.val c.val)) = true := by decide +kernel
theorem in670_sf : ∀ a b : Fin 16, in670adjB a b = true → ∀ c : Fin 16, in670adjB a c = true →
    in670adjB b c = true → in670UC.contains (in670ec a.val b.val) = true →
    in670UC.contains (in670ec a.val c.val) = false → in670UC.contains (in670ec b.val c.val) = false →
    in670FC.contains (in670ec a.val b.val) = true := by decide +kernel
theorem in670_c5 : ∀ t ∈ in670PL, ∀ x ∈ in670tc t, ∀ y ∈ in670tc t, x ≠ y →
    ¬ (in670FC.contains x = true ∧ in670FC.contains y = true) := by decide +kernel
theorem in670_ne_P : ∀ p ∈ in670PL, in670F p.1 ≠ in670F p.2.1 ∧ in670F p.1 ≠ in670F p.2.2 ∧ in670F p.2.1 ≠ in670F p.2.2 := by decide +kernel

theorem simple_graph_maximal_packing_single_forced_edge_support_counterexample :
    ∃ (G : SimpleGraph (Fin 16)) (P Q : Finset (Finset (Fin 16))),
      P.card = 5 ∧ (∀ p ∈ P, G.IsNClique 3 p) ∧
      (P : Set (Finset (Fin 16))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ∧
      (∀ t : Finset (Fin 16), G.IsNClique 3 t →
        ¬ Disjoint (finite_vertex_set_edge_encoding t)
          ((P.image finite_vertex_set_edge_encoding).biUnion id)) ∧
      (∀ p ∈ P, ∀ e f : Sym2 (Fin 16),
        e ∈ finite_vertex_set_edge_encoding p → f ∈ finite_vertex_set_edge_encoding p → e ≠ f →
        ¬ ((∃ t : Finset (Fin 16), G.IsNClique 3 t ∧
              finite_vertex_set_edge_encoding t ∩ ((P.image finite_vertex_set_edge_encoding).biUnion id) = {e}) ∧
           (∃ t : Finset (Fin 16), G.IsNClique 3 t ∧
              finite_vertex_set_edge_encoding t ∩ ((P.image finite_vertex_set_edge_encoding).biUnion id) = {f}))) ∧
      (∀ C : Finset (Sym2 (Fin 16)), C ⊆ (P.image finite_vertex_set_edge_encoding).biUnion id →
        C.card ≤ 10 → ∃ t : Finset (Fin 16), G.IsNClique 3 t ∧
          Disjoint C (finite_vertex_set_edge_encoding t)) ∧
      Q.card = 9 ∧ (∀ q ∈ Q, G.IsNClique 3 q) ∧
      (Q : Set (Finset (Fin 16))).Pairwise (fun a b => (a ∩ b).card ≤ 1) := by
  classical
  have hcliqueT : ∀ t ∈ in670TL, in670G.IsNClique 3 (in670e3 t) := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := in670_TL_adj t ht
    exact SimpleGraph.is3Clique_triple_iff.2
      ⟨(in670_adj_iff _ _).2 h1, (in670_adj_iff _ _).2 h2, (in670_adj_iff _ _).2 h3⟩
  set P : Finset (Finset (Fin 16)) := (in670PL.map in670e3).toFinset with hP
  set Q : Finset (Finset (Fin 16)) := (in670QL.map in670e3).toFinset with hQ
  set U : Finset (Sym2 (Fin 16)) := (P.image finite_vertex_set_edge_encoding).biUnion id with hU
  have hUcode : ∀ e ∈ U, in670UC.contains (in670sc e) = true := by
    intro e he
    obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.1 he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp)
    have h1 := in670_enc3_codes u e hes
    simp only [in670UC, List.contains_iff_mem, List.mem_flatMap]
    exact ⟨u, hu, h1⟩
  have hcodeU : ∀ x y : Fin 16, x ≠ y → in670UC.contains (in670ec x.val y.val) = true → s(x, y) ∈ U := by
    intro x y hxy h
    simp only [in670UC, List.contains_iff_mem, List.mem_flatMap] at h
    obtain ⟨p, hp, hc⟩ := h
    obtain ⟨n1, n2, n3⟩ := in670_ne_P p hp
    have hmem : ∀ u v : Fin 16, u ∈ in670e3 p → v ∈ in670e3 p → u ≠ v →
        in670ec x.val y.val = in670ec u.val v.val → s(x, y) ∈ U := by
      intro u v hu hv huv he
      rw [in670_ec_inj x y u v he]
      refine Finset.mem_biUnion.2 ⟨finite_vertex_set_edge_encoding (in670e3 p), ?_, in670_mem_enc _ u v hu hv huv⟩
      exact Finset.mem_image.2 ⟨in670e3 p, List.mem_toFinset.2 (List.mem_map.2 ⟨p, hp, rfl⟩), rfl⟩
    simp only [in670tc, List.mem_cons, List.not_mem_nil, or_false] at hc
    have hv : ∀ n : ℕ, n % 16 = (in670F n).val := fun n => rfl
    simp only [hv] at hc
    rcases hc with h | h | h
    · exact hmem _ _ (by simp [in670e3]) (by simp [in670e3]) n1 h
    · exact hmem _ _ (by simp [in670e3]) (by simp [in670e3]) n2 h
    · exact hmem _ _ (by simp [in670e3]) (by simp [in670e3]) n3 h
  have hsfcase : ∀ a b c : Fin 16, in670G.Adj a b → in670G.Adj a c → in670G.Adj b c →
      (finite_vertex_set_edge_encoding ({a, b, c} : Finset (Fin 16)) ∩ U = {s(a, b)}) →
      in670FC.contains (in670ec a.val b.val) = true := by
    intro a b c hab hac hbc hx
    have hne1 := hab.ne
    have hne2 := hac.ne
    have hne3 := hbc.ne
    have hmem : s(a, b) ∈ finite_vertex_set_edge_encoding ({a, b, c} : Finset (Fin 16)) ∩ U := by
      rw [hx]; exact Finset.mem_singleton_self _
    have h1 : in670UC.contains (in670ec a.val b.val) = true := hUcode _ (Finset.mem_inter.1 hmem).2
    have h2 : in670UC.contains (in670ec a.val c.val) = false := by
      by_contra hcon
      have hcon' : in670UC.contains (in670ec a.val c.val) = true := by simpa using hcon
      have hin : s(a, c) ∈ finite_vertex_set_edge_encoding ({a, b, c} : Finset (Fin 16)) ∩ U :=
        Finset.mem_inter.2 ⟨in670_mem_enc _ a c (by simp) (by simp) hne2, hcodeU a c hne2 hcon'⟩
      rw [hx, Finset.mem_singleton, Sym2.eq_iff] at hin
      rcases hin with ⟨_, h⟩ | ⟨h, _⟩
      · exact hne3 h.symm
      · exact hne1 h
    have h3 : in670UC.contains (in670ec b.val c.val) = false := by
      by_contra hcon
      have hcon' : in670UC.contains (in670ec b.val c.val) = true := by simpa using hcon
      have hin : s(b, c) ∈ finite_vertex_set_edge_encoding ({a, b, c} : Finset (Fin 16)) ∩ U :=
        Finset.mem_inter.2 ⟨in670_mem_enc _ b c (by simp) (by simp) hne3, hcodeU b c hne3 hcon'⟩
      rw [hx, Finset.mem_singleton, Sym2.eq_iff] at hin
      rcases hin with ⟨h, _⟩ | ⟨h, h'⟩
      · exact hne1 h.symm
      · exact hne2 h'.symm
    exact in670_sf a b ((in670_adj_iff _ _).1 hab) c ((in670_adj_iff _ _).1 hac)
      ((in670_adj_iff _ _).1 hbc) h1 h2 h3
  have hsfcode : ∀ (t : Finset (Fin 16)) (e : Sym2 (Fin 16)), in670G.IsNClique 3 t →
      finite_vertex_set_edge_encoding t ∩ U = {e} → in670FC.contains (in670sc e) = true := by
    intro t e ht hte
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.1 ht
    have hemem : e ∈ finite_vertex_set_edge_encoding ({a, b, c} : Finset (Fin 16)) := by
      have : e ∈ finite_vertex_set_edge_encoding ({a, b, c} : Finset (Fin 16)) ∩ U := by
        rw [hte]; exact Finset.mem_singleton_self _
      exact (Finset.mem_inter.1 this).1
    have hcode := in670_enc3_fin a b c e hemem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    rcases hcode with h | h | h
    · have hes : e = s(a, b) := in670_sc_inj (by
        rw [h]; rfl)
      subst hes
      exact hsfcase a b c hab hac hbc hte
    · have hes : e = s(a, c) := in670_sc_inj (by
        rw [h]; rfl)
      subst hes
      have he2 : ({a, c, b} : Finset (Fin 16)) = {a, b, c} := by
        rw [Finset.pair_comm]
      refine hsfcase a c b hac hab hbc.symm ?_
      rw [he2]; exact hte
    · have hes : e = s(b, c) := in670_sc_inj (by
        rw [h]; rfl)
      subst hes
      have he2 : ({b, c, a} : Finset (Fin 16)) = {a, b, c} := by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      refine hsfcase b c a hbc hab.symm hac.symm ?_
      rw [he2]; exact hte
  refine ⟨in670G, P, Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hP, List.toFinset_card_of_nodup in670_P_nodup, List.length_map, in670_P_len]
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp)
    exact hcliqueT u (in670_P_sub u hu)
  · intro a ha b hb hab
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ha)
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hb)
    have hne : u ≠ v := fun e => hab (by rw [e])
    exact in670_card_inter u v (in670_P_pw u hu v hv hne)
  · intro t ht hd
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.1 ht
    have hc := in670_c4 a b ((in670_adj_iff _ _).1 hab) c ((in670_adj_iff _ _).1 hac)
      ((in670_adj_iff _ _).1 hbc)
    simp only [Bool.or_eq_true] at hc
    have hfin : ∀ x y : Fin 16, x ∈ ({a, b, c} : Finset (Fin 16)) → y ∈ ({a, b, c} : Finset (Fin 16)) →
        x ≠ y → in670UC.contains (in670ec x.val y.val) = true → False := by
      intro x y hx hy hne hmem
      exact Finset.disjoint_left.1 hd (in670_mem_enc _ x y hx hy hne) (hcodeU x y hne hmem)
    rcases hc with (h | h) | h
    · exact hfin a b (by simp) (by simp) hab.ne h
    · exact hfin a c (by simp) (by simp) hac.ne h
    · exact hfin b c (by simp) (by simp) hbc.ne h
  · intro p hp e f he hf hne ⟨⟨t1, ht1, hs1⟩, ⟨t2, ht2, hs2⟩⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp)
    have he1 := in670_enc3_codes u e he
    have hf1 := in670_enc3_codes u f hf
    exact in670_c5 u hu _ he1 _ hf1 (fun h => hne (in670_sc_inj h))
      ⟨hsfcode t1 e ht1 hs1, hsfcode t2 f ht2 hs2⟩
  · intro C hC hcard
    by_contra hcon
    push Not at hcon
    have hhit : ∀ r ∈ in670TR, ∃ x ∈ r, x ∈ C.image in670sc := by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hr
      have hnd := hcon (in670e3 t) (hcliqueT t ht)
      obtain ⟨e, heC, het⟩ := Finset.not_disjoint_iff.1 hnd
      refine ⟨in670sc e, ?_, Finset.mem_image_of_mem _ heC⟩
      exact List.mem_filter.2 ⟨in670_enc3_codes t e het, hUcode e (hC heC)⟩
    have := in670_nh_spec (C.image in670sc) hhit 10 [] in670_nh10 List.nodup_nil (by simp)
    apply this
    rw [Finset.card_image_of_injective _ in670_sc_inj]
    simp only [List.length_nil]
    omega
  · rw [hQ, List.toFinset_card_of_nodup in670_Q_nodup, List.length_map, in670_Q_len]
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp)
    exact hcliqueT u (in670_Q_sub u hu)
  · intro a ha b hb hab
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ha)
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hb)
    have hne : u ≠ v := fun e => hab (by rw [e])
    exact in670_card_inter u v (in670_Q_pw u hu v hv hne)
