import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_stable_lex_outside_forces_triangle_example

Topic: graphs   Node: 83491f88201f

Provenance: helper lemma. Exact experiments 16086 and independently 16087.

There is an edge-stable eight-vertex graph and maximum triangle packing P such that every minimum triangle cover minimizing its outside-P edges contains two outside-P edges of the same triangle.
-/

open scoped Sym2


def sg665g_maxC {α : Type} (c : α → α → Bool) : ℕ → List α → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, t :: l => max (sg665g_maxC c n l) (1 + sg665g_maxC c n (l.filter (c t)))

theorem sg665g_maxC_bound {α : Type} [DecidableEq α] (c : α → α → Bool) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ S : Finset α, (∀ a ∈ S, a ∈ l) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → c a b = true) → S.card ≤ sg665g_maxC c n l := by
  intro n
  induction n with
  | zero =>
    intro l hl S hS _
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst hl0
    have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
    simp [this, sg665g_maxC]
  | succ n ih =>
    intro l hl S hS hc
    match l, hl, hS with
    | [], _, hS =>
      have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
      simp [this, sg665g_maxC]
    | t :: l, hl, hS =>
      rw [sg665g_maxC]
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

def sg665g_enum {E : Type} [DecidableEq E] : ℕ → List (List E) → List (List E)
  | _, [] => [[]]
  | 0, _ :: _ => []
  | k + 1, l :: F => l.flatMap fun e => (sg665g_enum k (F.filter fun l' => decide (e ∉ l'))).map (e :: ·)

theorem sg665g_enum_complete {E : Type} [DecidableEq E] :
    ∀ (k : ℕ) (F : List (List E)) (D : Finset E), (∀ l ∈ F, ∃ e ∈ D, e ∈ l) → D.card ≤ k →
      ∃ s ∈ sg665g_enum k F, s.toFinset ⊆ D := by
  intro k
  induction k with
  | zero =>
    intro F D hD hc
    match F, hD with
    | [], _ => exact ⟨[], by simp [sg665g_enum], by simp⟩
    | l :: F, hD =>
      obtain ⟨e, he, _⟩ := hD l (by simp)
      have : D = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [this] at he
  | succ k ih =>
    intro F D hD hc
    match F, hD with
    | [], _ => exact ⟨[], by simp [sg665g_enum], by simp⟩
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
      · simp only [sg665g_enum, List.mem_flatMap, List.mem_map]
        exact ⟨e, hel, s, hs, rfl⟩
      · intro x hx
        simp only [List.toFinset_cons, Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact he
        · exact (Finset.mem_erase.mp (hsD hx)).2
def sg665_EL : List (Sym2 (Fin 8)) :=
  [s(0,3), s(0,4), s(0,5), s(0,6), s(0,7), s(1,3), s(1,4), s(1,5), s(1,6), s(1,7), s(2,5), s(2,6), s(2,7), s(3,4), s(3,5), s(3,6), s(3,7), s(4,5), s(4,6), s(4,7), s(5,6), s(5,7), s(6,7)]
def sg665_T : List (Finset (Fin 8)) := [{0,3,4}, {0,3,5}, {0,3,6}, {0,3,7}, {0,4,5}, {0,4,6}, {0,4,7}, {0,5,6}, {0,5,7}, {0,6,7}, {1,3,4}, {1,3,5}, {1,3,6}, {1,3,7}, {1,4,5}, {1,4,6}, {1,4,7}, {1,5,6}, {1,5,7}, {1,6,7}, {2,5,6}, {2,5,7}, {2,6,7}, {3,4,5}, {3,4,6}, {3,4,7}, {3,5,6}, {3,5,7}, {3,6,7}, {4,5,6}, {4,5,7}, {4,6,7}, {5,6,7}]
def sg665_W : List (Sym2 (Fin 8) × List (Finset (Fin 8))) := [(s(0,3), [{0,4,5}, {0,6,7}, {1,3,5}, {1,4,6}, {2,5,6}, {3,4,7}]), (s(0,4), [{0,3,5}, {0,6,7}, {1,3,6}, {1,4,5}, {2,5,6}, {3,4,7}]), (s(0,5), [{0,3,4}, {0,6,7}, {1,3,5}, {1,4,6}, {2,5,6}, {4,5,7}]), (s(0,6), [{0,3,4}, {0,5,7}, {1,3,5}, {1,4,6}, {2,5,6}, {3,6,7}]), (s(0,7), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,5,7}, {3,6,7}]), (s(1,3), [{0,3,5}, {0,4,6}, {1,4,5}, {1,6,7}, {2,5,6}, {3,4,7}]), (s(1,4), [{0,3,5}, {0,4,6}, {1,3,6}, {1,5,7}, {2,5,6}, {3,4,7}]), (s(1,5), [{0,3,4}, {0,5,6}, {1,3,6}, {1,4,7}, {2,6,7}, {3,5,7}]), (s(1,6), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,7}, {2,5,7}, {3,6,7}]), (s(1,7), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,5,7}, {3,6,7}]), (s(2,5), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,6,7}, {4,5,7}]), (s(2,6), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,5,7}, {3,6,7}]), (s(2,7), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {3,6,7}, {4,5,7}]), (s(3,4), [{0,3,5}, {0,4,6}, {1,3,7}, {1,5,6}, {2,6,7}, {4,5,7}]), (s(3,5), [{0,3,4}, {0,5,6}, {1,3,6}, {1,4,5}, {2,5,7}, {4,6,7}]), (s(3,6), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,6,7}, {4,5,7}]), (s(3,7), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,6,7}, {4,5,7}]), (s(4,5), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,5,7}, {3,6,7}]), (s(4,6), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,7}, {2,5,7}, {3,6,7}]), (s(4,7), [{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,5,7}, {3,6,7}]), (s(5,6), [{0,3,5}, {0,4,6}, {1,3,6}, {1,4,5}, {2,5,7}, {3,4,7}]), (s(5,7), [{0,3,5}, {0,4,6}, {1,3,6}, {1,4,5}, {2,5,6}, {3,4,7}]), (s(6,7), [{0,3,5}, {0,4,6}, {1,3,6}, {1,4,5}, {2,5,6}, {3,4,7}])]

def sg665_P : Finset (Finset (Fin 8)) := {{0,3,5},{0,4,6},{1,3,6},{1,4,5},{2,5,6},{3,4,7}}
def sg665_C : Finset (Sym2 (Fin 8)) := {s(0,3), s(1,3), s(4,5), s(4,6), s(4,7), s(5,6), s(5,7), s(6,7)}
def sg665_U : Finset (Sym2 (Fin 8)) := (sg665_P.image finite_vertex_set_edge_encoding).biUnion id

def sg665_E : Finset (Sym2 (Fin 8)) := sg665_EL.toFinset

def sg665_G : SimpleGraph (Fin 8) where
  Adj u v := s(u,v) ∈ sg665_E ∧ u ≠ v
  symm := Std.Symm.mk (fun u v h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩)
  loopless := Std.Irrefl.mk (fun u h => h.2 rfl)

instance sg665_dec : DecidableRel sg665_G.Adj :=
  fun u v => decidable_of_decidable_of_iff (p := s(u,v) ∈ sg665_E ∧ u ≠ v) (q := sg665_G.Adj u v) Iff.rfl

set_option maxRecDepth 100000 in
theorem sg665_tri_complete : ∀ t ∈ (Finset.univ : Finset (Fin 8)).powersetCard 3,
    sg665_G.IsNClique 3 t → t ∈ sg665_T := by decide +kernel

set_option maxRecDepth 100000 in
theorem sg665_T_clique : ∀ t ∈ sg665_T, sg665_G.IsNClique 3 t := by decide +kernel

lemma sg665_clique_mem {t : Finset (Fin 8)} (h : sg665_G.IsNClique 3 t) : t ∈ sg665_T :=
  sg665_tri_complete t (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h.card_eq⟩) h

lemma sg665_edge_mem {g : Sym2 (Fin 8)} (h : g ∈ sg665_G.edgeSet) : g ∈ sg665_EL := by
  induction g using Sym2.ind with
  | _ a b =>
    have h1 := ((SimpleGraph.mem_edgeSet sg665_G).mp h).1
    exact List.mem_toFinset.mp h1

def sg665_compat (s t : Finset (Fin 8)) : Bool := decide ((s ∩ t).card ≤ 1)

set_option maxRecDepth 100000 in
theorem sg665_maxC_eq : sg665g_maxC sg665_compat sg665_T.length sg665_T = 6 := by decide +kernel

lemma sg665_nu_le (T : Finset (Finset (Fin 8))) (hT : ∀ t ∈ T, sg665_G.IsNClique 3 t)
    (hP : (T : Set (Finset (Fin 8))).Pairwise (fun a b => (a ∩ b).card ≤ 1)) : T.card ≤ 6 :=
  calc T.card ≤ sg665g_maxC sg665_compat sg665_T.length sg665_T :=
        sg665g_maxC_bound sg665_compat _ sg665_T le_rfl T (fun a ha => sg665_clique_mem (hT a ha))
          (fun a ha b hb hab => decide_eq_true (hP (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab))
    _ = 6 := sg665_maxC_eq

theorem sg665_P_clique : ∀ t ∈ sg665_P, sg665_G.IsNClique 3 t := by decide +kernel

theorem sg665_P_pw' : ∀ a ∈ sg665_P, ∀ b ∈ sg665_P, a ≠ b → (a ∩ b).card ≤ 1 := by decide +kernel

lemma sg665_P_pw : (sg665_P : Set (Finset (Fin 8))).Pairwise (fun a b => (a ∩ b).card ≤ 1) :=
  fun a ha b hb hab => sg665_P_pw' a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab

theorem sg665_P_card : sg665_P.card = 6 := by decide +kernel

theorem sg665_pack_eq : simple_graph_triangle_packing_number sg665_G = 6 := by
  unfold simple_graph_triangle_packing_number
  refine IsGreatest.csSup_eq ⟨⟨sg665_P, sg665_P_clique, sg665_P_pw, sg665_P_card⟩, ?_⟩
  rintro n ⟨T, h1, h2, rfl⟩
  exact sg665_nu_le T h1 h2

set_option maxRecDepth 100000 in
theorem sg665_W_cover : ∀ g ∈ sg665_EL, ∃ q ∈ sg665_W, q.1 = g := by decide +kernel

set_option maxRecDepth 100000 in
theorem sg665_W_ok : ∀ q ∈ sg665_W, q.2.toFinset.card = 6 ∧
    (∀ t ∈ q.2, t ∈ sg665_T ∧ ¬ ∀ x ∈ q.1, x ∈ t) ∧
    (∀ a ∈ q.2, ∀ b ∈ q.2, a ≠ b → (a ∩ b).card ≤ 1) := by decide +kernel

lemma sg665_del_clique {t : Finset (Fin 8)} {g : Sym2 (Fin 8)} (h : sg665_G.IsNClique 3 t)
    (hg : ¬ ∀ x ∈ g, x ∈ t) : (sg665_G.deleteEdges {g}).IsNClique 3 t := by
  refine ⟨?_, h.card_eq⟩
  intro a ha b hb hab
  refine (SimpleGraph.deleteEdges_adj).mpr ⟨h.isClique ha hb hab, ?_⟩
  intro hmem
  have hgeq : s(a,b) = g := Set.mem_singleton_iff.mp hmem
  apply hg
  rw [← hgeq]
  intro x hx
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact ha
  · exact hb

theorem sg665_stable : ∀ g ∈ sg665_G.edgeSet,
    simple_graph_triangle_packing_number (sg665_G.deleteEdges {g}) = simple_graph_triangle_packing_number sg665_G := by
  intro g hg
  rw [sg665_pack_eq]
  obtain ⟨q, hq, rfl⟩ := sg665_W_cover g (sg665_edge_mem hg)
  obtain ⟨h1, h2, h3⟩ := sg665_W_ok q hq
  unfold simple_graph_triangle_packing_number
  refine IsGreatest.csSup_eq ⟨⟨q.2.toFinset, ?_, ?_, h1⟩, ?_⟩
  · intro t ht
    have ht' := List.mem_toFinset.mp ht
    exact sg665_del_clique (sg665_T_clique t (h2 t ht').1) (h2 t ht').2
  · intro a ha b hb hab
    exact h3 a (List.mem_toFinset.mp (Finset.mem_coe.mp ha)) b (List.mem_toFinset.mp (Finset.mem_coe.mp hb)) hab
  · rintro n ⟨T, hT, hP, rfl⟩
    exact sg665_nu_le T (fun t ht => (hT t ht).mono (SimpleGraph.deleteEdges_le _)) hP

def sg665_F : List (List (Sym2 (Fin 8))) :=
  sg665_T.map fun t => sg665_EL.filter (fun g => decide (∀ x ∈ g, x ∈ t))

set_option maxRecDepth 100000 in
theorem sg665_enum_small : sg665g_enum (8 - 1) sg665_F = [] := by decide +kernel

theorem sg665_C_mem : ∀ g ∈ sg665_C, g ∈ sg665_E ∧ ¬ g.IsDiag := by decide +kernel

lemma sg665_C_edge : ∀ g ∈ sg665_C, g ∈ sg665_G.edgeSet := by
  intro g hg
  obtain ⟨h1, h2⟩ := sg665_C_mem g hg
  induction g using Sym2.ind with
  | _ a b => exact (SimpleGraph.mem_edgeSet sg665_G).mpr ⟨h1, fun h => h2 (Sym2.mk_isDiag_iff.mpr h)⟩

theorem sg665_C_cover : ∀ t ∈ sg665_T, ∃ g ∈ sg665_C, ∀ x ∈ g, x ∈ t := by decide +kernel
theorem sg665_C_card : sg665_C.card = 8 := by decide +kernel

lemma sg665_hit (D : Finset (Sym2 (Fin 8))) (hE : ∀ g ∈ D, g ∈ sg665_G.edgeSet)
    (hC : ∀ t : Finset (Fin 8), sg665_G.IsNClique 3 t → ∃ g ∈ D, ∀ x ∈ g, x ∈ t) :
    ∀ l ∈ sg665_F, ∃ e ∈ D, e ∈ l := by
  intro l hl
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
  obtain ⟨g, hg, hgt⟩ := hC t (sg665_T_clique t ht)
  exact ⟨g, hg, List.mem_filter.mpr ⟨sg665_edge_mem (hE g hg), decide_eq_true hgt⟩⟩

theorem sg665_tau_eq : simple_graph_triangle_cover_number sg665_G = 8 := by
  unfold simple_graph_triangle_cover_number
  refine IsLeast.csInf_eq ⟨⟨sg665_C, sg665_C_edge, ?_, sg665_C_card⟩, ?_⟩
  · intro t ht
    exact sg665_C_cover t (sg665_clique_mem ht)
  · rintro n ⟨D, hE, hC, rfl⟩
    by_contra hlt
    obtain ⟨s, hs, _⟩ := sg665g_enum_complete (8 - 1) sg665_F D (sg665_hit D hE hC) (by omega)
    rw [sg665_enum_small] at hs
    simp at hs


set_option maxRecDepth 100000 in
theorem sg665_leaf : ∀ s ∈ sg665g_enum 8 sg665_F, s.toFinset.card = 8 ∧ (sg665_C \ sg665_U).card ≤ (s.toFinset \ sg665_U).card
    ∧ s(5,7) ∈ s.toFinset \ sg665_U ∧ s(6,7) ∈ s.toFinset \ sg665_U := by decide +kernel

lemma sg665_D_eq (D : Finset (Sym2 (Fin 8))) (hE : ∀ g ∈ D, g ∈ sg665_G.edgeSet)
    (hC : ∀ t : Finset (Fin 8), sg665_G.IsNClique 3 t → ∃ g ∈ D, ∀ x ∈ g, x ∈ t)
    (hcard : D.card = 8) : (sg665_C \ sg665_U).card ≤ (D \ sg665_U).card ∧ s(5,7) ∈ D \ sg665_U ∧ s(6,7) ∈ D \ sg665_U := by
  obtain ⟨s, hs, hsub⟩ := sg665g_enum_complete 8 sg665_F D (sg665_hit D hE hC) (by omega)
  obtain ⟨h1, h2⟩ := sg665_leaf s hs
  have heq : s.toFinset = D := Finset.eq_of_subset_of_card_le hsub (by rw [h1, hcard])
  rw [heq] at h2
  exact h2

theorem sg665_t57 : ({5,6,7} : Finset (Fin 8)) ∈ sg665_T := by decide +kernel
theorem sg665_ne : (s(5,7) : Sym2 (Fin 8)) ≠ s(6,7) := by decide +kernel
theorem sg665_e_in : ∀ x ∈ (s(5,7) : Sym2 (Fin 8)), x ∈ ({5,6,7} : Finset (Fin 8)) := by decide +kernel
theorem sg665_f_in : ∀ x ∈ (s(6,7) : Sym2 (Fin 8)), x ∈ ({5,6,7} : Finset (Fin 8)) := by decide +kernel

theorem simple_graph_stable_lex_outside_forces_triangle_example :
    ∃ (G : SimpleGraph (Fin 8)) (P : Finset (Finset (Fin 8)))
      (C : Finset (Sym2 (Fin 8))),
      simple_graph_triangle_packing_number G = 6 ∧ simple_graph_triangle_cover_number G = 8 ∧
      (∀ g ∈ G.edgeSet,
        simple_graph_triangle_packing_number (G.deleteEdges {g}) =
          simple_graph_triangle_packing_number G) ∧
      (∀ s ∈ P, G.IsNClique 3 s) ∧
      (P : Set (Finset (Fin 8))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ∧
      P.card = simple_graph_triangle_packing_number G ∧
      (∀ g ∈ C, g ∈ G.edgeSet) ∧
      (∀ s : Finset (Fin 8), G.IsNClique 3 s → ∃ g ∈ C, ∀ x ∈ g, x ∈ s) ∧
      C.card = simple_graph_triangle_cover_number G ∧
      (∀ D : Finset (Sym2 (Fin 8)),
        (∀ g ∈ D, g ∈ G.edgeSet) →
        (∀ s : Finset (Fin 8), G.IsNClique 3 s → ∃ g ∈ D, ∀ x ∈ g, x ∈ s) →
        D.card = simple_graph_triangle_cover_number G →
        (C \ (P.image finite_vertex_set_edge_encoding).biUnion id).card ≤
          (D \ (P.image finite_vertex_set_edge_encoding).biUnion id).card) ∧
      ∀ D : Finset (Sym2 (Fin 8)),
        (∀ g ∈ D, g ∈ G.edgeSet) →
        (∀ s : Finset (Fin 8), G.IsNClique 3 s → ∃ g ∈ D, ∀ x ∈ g, x ∈ s) →
        D.card = simple_graph_triangle_cover_number G →
        (D \ (P.image finite_vertex_set_edge_encoding).biUnion id).card =
          (C \ (P.image finite_vertex_set_edge_encoding).biUnion id).card →
        ∃ (t : Finset (Fin 8)) (e f : Sym2 (Fin 8)),
          G.IsNClique 3 t ∧ e ≠ f ∧
          e ∈ D \ (P.image finite_vertex_set_edge_encoding).biUnion id ∧
          f ∈ D \ (P.image finite_vertex_set_edge_encoding).biUnion id ∧
          (∀ x ∈ e, x ∈ t) ∧ (∀ x ∈ f, x ∈ t) := by
  refine ⟨sg665_G, sg665_P, sg665_C, sg665_pack_eq, sg665_tau_eq, sg665_stable, sg665_P_clique, sg665_P_pw, ?_,
    sg665_C_edge, fun t ht => sg665_C_cover t (sg665_clique_mem ht), ?_, ?_, ?_⟩
  · rw [sg665_P_card, sg665_pack_eq]
  · rw [sg665_C_card, sg665_tau_eq]
  · intro D hE hC hcard
    rw [sg665_tau_eq] at hcard
    exact (sg665_D_eq D hE hC hcard).1
  · intro D hE hC hcard _
    rw [sg665_tau_eq] at hcard
    obtain ⟨_, h2, h3⟩ := sg665_D_eq D hE hC hcard
    exact ⟨{5,6,7}, s(5,7), s(6,7), sg665_T_clique _ sg665_t57, sg665_ne, h2, h3, sg665_e_in, sg665_f_in⟩
