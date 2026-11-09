import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_stable_lex_private_triangle_direct_exchange_counterexample

Topic: graphs   Node: 3e7e881e06b3

Provenance: helper lemma. Exact computations 16067–16069; triangle packing and cover definitions from arXiv:2610.15539, Section 1.

There is a stable graph with a unique minimum triangle edge cover and a maximum packing such that the cover has exactly one edge outside the packing, but every private triangle of that edge intersects at least two packed triangles. Thus no such private triangle can be inserted by replacing only one packed triangle.
-/

open scoped Sym2


def sgx_maxC {α : Type} (c : α → α → Bool) : ℕ → List α → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, t :: l => max (sgx_maxC c n l) (1 + sgx_maxC c n (l.filter (c t)))

theorem sgx_maxC_bound {α : Type} [DecidableEq α] (c : α → α → Bool) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ S : Finset α, (∀ a ∈ S, a ∈ l) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → c a b = true) → S.card ≤ sgx_maxC c n l := by
  intro n
  induction n with
  | zero =>
    intro l hl S hS _
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst hl0
    have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
    simp [this, sgx_maxC]
  | succ n ih =>
    intro l hl S hS hc
    match l, hl, hS with
    | [], _, hS =>
      have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
      simp [this, sgx_maxC]
    | t :: l, hl, hS =>
      rw [sgx_maxC]
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

def sgx_enum {E : Type} [DecidableEq E] : ℕ → List (List E) → List (List E)
  | _, [] => [[]]
  | 0, _ :: _ => []
  | k + 1, l :: F => l.flatMap fun e => (sgx_enum k (F.filter fun l' => decide (e ∉ l'))).map (e :: ·)

theorem sgx_enum_complete {E : Type} [DecidableEq E] :
    ∀ (k : ℕ) (F : List (List E)) (D : Finset E), (∀ l ∈ F, ∃ e ∈ D, e ∈ l) → D.card ≤ k →
      ∃ s ∈ sgx_enum k F, s.toFinset ⊆ D := by
  intro k
  induction k with
  | zero =>
    intro F D hD hc
    match F, hD with
    | [], _ => exact ⟨[], by simp [sgx_enum], by simp⟩
    | l :: F, hD =>
      obtain ⟨e, he, _⟩ := hD l (by simp)
      have : D = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [this] at he
  | succ k ih =>
    intro F D hD hc
    match F, hD with
    | [], _ => exact ⟨[], by simp [sgx_enum], by simp⟩
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
      · simp only [sgx_enum, List.mem_flatMap, List.mem_map]
        exact ⟨e, hel, s, hs, rfl⟩
      · intro x hx
        simp only [List.toFinset_cons, Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact he
        · exact (Finset.mem_erase.mp (hsD hx)).2
def sx_EL : List (Sym2 (Fin 8)) :=
  [s(0,4), s(0,5), s(0,7), s(1,4), s(1,6), s(1,7), s(2,5), s(2,6), s(2,7), s(3,5), s(3,6), s(3,7), s(4,5), s(4,6), s(4,7), s(5,6), s(5,7), s(6,7)]
def sx_T : List (Finset (Fin 8)) := [{0,4,5}, {0,4,7}, {0,5,7}, {1,4,6}, {1,4,7}, {1,6,7}, {2,5,6}, {2,5,7}, {2,6,7}, {3,5,6}, {3,5,7}, {3,6,7}, {4,5,6}, {4,5,7}, {4,6,7}, {5,6,7}]
def sx_W : List (Sym2 (Fin 8) × List (Finset (Fin 8))) := [(s(0,4), [{0,5,7}, {1,4,6}, {2,5,6}, {3,6,7}]), (s(0,5), [{0,4,7}, {1,4,6}, {2,5,6}, {3,5,7}]), (s(0,7), [{0,4,5}, {1,4,6}, {2,5,6}, {3,5,7}]), (s(1,4), [{0,4,5}, {1,6,7}, {2,5,6}, {3,5,7}]), (s(1,6), [{0,4,5}, {1,4,7}, {2,5,6}, {3,5,7}]), (s(1,7), [{0,4,5}, {1,4,6}, {2,5,6}, {3,5,7}]), (s(2,5), [{0,4,5}, {1,4,6}, {2,6,7}, {3,5,6}]), (s(2,6), [{0,4,5}, {1,4,6}, {2,5,7}, {3,5,6}]), (s(2,7), [{0,4,5}, {1,4,6}, {2,5,6}, {3,5,7}]), (s(3,5), [{0,4,5}, {1,4,6}, {2,5,6}, {3,6,7}]), (s(3,6), [{0,4,5}, {1,4,6}, {2,5,6}, {3,5,7}]), (s(3,7), [{0,4,5}, {1,4,6}, {2,5,7}, {3,5,6}]), (s(4,5), [{0,4,7}, {1,4,6}, {2,5,6}, {3,5,7}]), (s(4,6), [{0,4,5}, {1,4,7}, {2,5,6}, {3,5,7}]), (s(4,7), [{0,4,5}, {1,4,6}, {2,5,6}, {3,5,7}]), (s(5,6), [{0,4,5}, {1,4,6}, {2,5,7}, {3,6,7}]), (s(5,7), [{0,4,5}, {1,4,6}, {2,5,6}, {3,6,7}]), (s(6,7), [{0,4,5}, {1,4,6}, {2,5,6}, {3,5,7}])]

def sx_P : Finset (Finset (Fin 8)) := {{0,4,7},{4,5,6},{1,6,7},{3,5,7}}
def sx_C : Finset (Sym2 (Fin 8)) := {s(0,4), s(1,4), s(5,6), s(5,7), s(6,7)}

def sx_E : Finset (Sym2 (Fin 8)) := sx_EL.toFinset

def sx_G : SimpleGraph (Fin 8) where
  Adj u v := s(u,v) ∈ sx_E ∧ u ≠ v
  symm := Std.Symm.mk (fun u v h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩)
  loopless := Std.Irrefl.mk (fun u h => h.2 rfl)

instance sx_dec : DecidableRel sx_G.Adj :=
  fun u v => decidable_of_decidable_of_iff (p := s(u,v) ∈ sx_E ∧ u ≠ v) (q := sx_G.Adj u v) Iff.rfl

set_option maxRecDepth 100000 in
theorem sx_tri_complete : ∀ t ∈ (Finset.univ : Finset (Fin 8)).powersetCard 3,
    sx_G.IsNClique 3 t → t ∈ sx_T := by decide +kernel

set_option maxRecDepth 100000 in
theorem sx_T_clique : ∀ t ∈ sx_T, sx_G.IsNClique 3 t := by decide +kernel

lemma sx_clique_mem {t : Finset (Fin 8)} (h : sx_G.IsNClique 3 t) : t ∈ sx_T :=
  sx_tri_complete t (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h.card_eq⟩) h

lemma sx_edge_mem {g : Sym2 (Fin 8)} (h : g ∈ sx_G.edgeSet) : g ∈ sx_EL := by
  induction g using Sym2.ind with
  | _ a b =>
    have h1 := ((SimpleGraph.mem_edgeSet sx_G).mp h).1
    exact List.mem_toFinset.mp h1

def sx_compat (s t : Finset (Fin 8)) : Bool := decide ((s ∩ t).card ≤ 1)

set_option maxRecDepth 100000 in
theorem sx_maxC_eq : sgx_maxC sx_compat sx_T.length sx_T = 4 := by decide +kernel

lemma sx_nu_le (T : Finset (Finset (Fin 8))) (hT : ∀ t ∈ T, sx_G.IsNClique 3 t)
    (hP : (T : Set (Finset (Fin 8))).Pairwise (fun a b => (a ∩ b).card ≤ 1)) : T.card ≤ 4 :=
  calc T.card ≤ sgx_maxC sx_compat sx_T.length sx_T :=
        sgx_maxC_bound sx_compat _ sx_T le_rfl T (fun a ha => sx_clique_mem (hT a ha))
          (fun a ha b hb hab => decide_eq_true (hP (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab))
    _ = 4 := sx_maxC_eq

theorem sx_P_clique : ∀ t ∈ sx_P, sx_G.IsNClique 3 t := by decide +kernel

theorem sx_P_pw' : ∀ a ∈ sx_P, ∀ b ∈ sx_P, a ≠ b → (a ∩ b).card ≤ 1 := by decide +kernel

lemma sx_P_pw : (sx_P : Set (Finset (Fin 8))).Pairwise (fun a b => (a ∩ b).card ≤ 1) :=
  fun a ha b hb hab => sx_P_pw' a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab

theorem sx_P_card : sx_P.card = 4 := by decide +kernel

theorem sx_pack_eq : simple_graph_triangle_packing_number sx_G = 4 := by
  unfold simple_graph_triangle_packing_number
  refine IsGreatest.csSup_eq ⟨⟨sx_P, sx_P_clique, sx_P_pw, sx_P_card⟩, ?_⟩
  rintro n ⟨T, h1, h2, rfl⟩
  exact sx_nu_le T h1 h2

set_option maxRecDepth 100000 in
theorem sx_W_cover : ∀ g ∈ sx_EL, ∃ q ∈ sx_W, q.1 = g := by decide +kernel

set_option maxRecDepth 100000 in
theorem sx_W_ok : ∀ q ∈ sx_W, q.2.toFinset.card = 4 ∧
    (∀ t ∈ q.2, t ∈ sx_T ∧ ¬ ∀ x ∈ q.1, x ∈ t) ∧
    (∀ a ∈ q.2, ∀ b ∈ q.2, a ≠ b → (a ∩ b).card ≤ 1) := by decide +kernel

lemma sx_del_clique {t : Finset (Fin 8)} {g : Sym2 (Fin 8)} (h : sx_G.IsNClique 3 t)
    (hg : ¬ ∀ x ∈ g, x ∈ t) : (sx_G.deleteEdges {g}).IsNClique 3 t := by
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

theorem sx_stable : ∀ g ∈ sx_G.edgeSet,
    simple_graph_triangle_packing_number (sx_G.deleteEdges {g}) = simple_graph_triangle_packing_number sx_G := by
  intro g hg
  rw [sx_pack_eq]
  obtain ⟨q, hq, rfl⟩ := sx_W_cover g (sx_edge_mem hg)
  obtain ⟨h1, h2, h3⟩ := sx_W_ok q hq
  unfold simple_graph_triangle_packing_number
  refine IsGreatest.csSup_eq ⟨⟨q.2.toFinset, ?_, ?_, h1⟩, ?_⟩
  · intro t ht
    have ht' := List.mem_toFinset.mp ht
    exact sx_del_clique (sx_T_clique t (h2 t ht').1) (h2 t ht').2
  · intro a ha b hb hab
    exact h3 a (List.mem_toFinset.mp (Finset.mem_coe.mp ha)) b (List.mem_toFinset.mp (Finset.mem_coe.mp hb)) hab
  · rintro n ⟨T, hT, hP, rfl⟩
    exact sx_nu_le T (fun t ht => (hT t ht).mono (SimpleGraph.deleteEdges_le _)) hP

def sx_F : List (List (Sym2 (Fin 8))) :=
  sx_T.map fun t => sx_EL.filter (fun g => decide (∀ x ∈ g, x ∈ t))

set_option maxRecDepth 100000 in
theorem sx_enum_small : sgx_enum (5 - 1) sx_F = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem sx_enum_exact : ∀ s ∈ sgx_enum 5 sx_F, s.toFinset = sx_C := by decide +kernel

theorem sx_C_mem : ∀ g ∈ sx_C, g ∈ sx_E ∧ ¬ g.IsDiag := by decide +kernel

lemma sx_C_edge : ∀ g ∈ sx_C, g ∈ sx_G.edgeSet := by
  intro g hg
  obtain ⟨h1, h2⟩ := sx_C_mem g hg
  induction g using Sym2.ind with
  | _ a b => exact (SimpleGraph.mem_edgeSet sx_G).mpr ⟨h1, fun h => h2 (Sym2.mk_isDiag_iff.mpr h)⟩

theorem sx_C_cover : ∀ t ∈ sx_T, ∃ g ∈ sx_C, ∀ x ∈ g, x ∈ t := by decide +kernel
theorem sx_C_card : sx_C.card = 5 := by decide +kernel

lemma sx_hit (D : Finset (Sym2 (Fin 8))) (hE : ∀ g ∈ D, g ∈ sx_G.edgeSet)
    (hC : ∀ t : Finset (Fin 8), sx_G.IsNClique 3 t → ∃ g ∈ D, ∀ x ∈ g, x ∈ t) :
    ∀ l ∈ sx_F, ∃ e ∈ D, e ∈ l := by
  intro l hl
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
  obtain ⟨g, hg, hgt⟩ := hC t (sx_T_clique t ht)
  exact ⟨g, hg, List.mem_filter.mpr ⟨sx_edge_mem (hE g hg), decide_eq_true hgt⟩⟩

theorem sx_tau_eq : simple_graph_triangle_cover_number sx_G = 5 := by
  unfold simple_graph_triangle_cover_number
  refine IsLeast.csInf_eq ⟨⟨sx_C, sx_C_edge, ?_, sx_C_card⟩, ?_⟩
  · intro t ht
    exact sx_C_cover t (sx_clique_mem ht)
  · rintro n ⟨D, hE, hC, rfl⟩
    by_contra hlt
    obtain ⟨s, hs, _⟩ := sgx_enum_complete (5 - 1) sx_F D (sx_hit D hE hC) (by omega)
    rw [sx_enum_small] at hs
    simp at hs

lemma sx_unique (D : Finset (Sym2 (Fin 8))) (hE : ∀ g ∈ D, g ∈ sx_G.edgeSet)
    (hC : ∀ t : Finset (Fin 8), sx_G.IsNClique 3 t → ∃ g ∈ D, ∀ x ∈ g, x ∈ t)
    (hcard : D.card = 5) : D = sx_C := by
  obtain ⟨s, hs, hsub⟩ := sgx_enum_complete 5 sx_F D (sx_hit D hE hC) (by omega)
  rw [sx_enum_exact s hs] at hsub
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, sx_C_card])).symm

set_option maxRecDepth 100000 in
theorem sx_outside : sx_C \ (sx_P.image finite_vertex_set_edge_encoding).biUnion id = {s(1,4)} := by decide +kernel

set_option maxRecDepth 100000 in
theorem sx_last : ∀ t ∈ sx_T, (∀ x ∈ (s(1,4) : Sym2 (Fin 8)), x ∈ t) →
    (∀ g ∈ sx_C, (∀ x ∈ g, x ∈ t) → g = s(1,4)) →
    2 ≤ (sx_P.filter fun s => 2 ≤ (s ∩ t).card).card := by decide +kernel

theorem simple_graph_stable_lex_private_triangle_direct_exchange_counterexample :
    ∃ (G : SimpleGraph (Fin 8)) (P : Finset (Finset (Fin 8)))
      (C : Finset (Sym2 (Fin 8))) (e : Sym2 (Fin 8)),
      simple_graph_triangle_packing_number G = 4 ∧
      simple_graph_triangle_cover_number G = 5 ∧
      (∀ g ∈ G.edgeSet,
        simple_graph_triangle_packing_number (G.deleteEdges {g}) =
          simple_graph_triangle_packing_number G) ∧
      (∀ t ∈ P, G.IsNClique 3 t) ∧
      (P : Set (Finset (Fin 8))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ∧
      P.card = simple_graph_triangle_packing_number G ∧
      (∀ g ∈ C, g ∈ G.edgeSet) ∧
      (∀ t : Finset (Fin 8), G.IsNClique 3 t → ∃ g ∈ C, ∀ x ∈ g, x ∈ t) ∧
      C.card = simple_graph_triangle_cover_number G ∧
      (∀ D : Finset (Sym2 (Fin 8)),
        (∀ g ∈ D, g ∈ G.edgeSet) →
        (∀ t : Finset (Fin 8), G.IsNClique 3 t → ∃ g ∈ D, ∀ x ∈ g, x ∈ t) →
        D.card = simple_graph_triangle_cover_number G → D = C) ∧
      C \ (P.image finite_vertex_set_edge_encoding).biUnion id = {e} ∧
      (∀ t : Finset (Fin 8), G.IsNClique 3 t →
        (∀ x ∈ e, x ∈ t) →
        (∀ g ∈ C, (∀ x ∈ g, x ∈ t) → g = e) →
        2 ≤ (P.filter fun s => 2 ≤ (s ∩ t).card).card) := by
  refine ⟨sx_G, sx_P, sx_C, s(1,4), sx_pack_eq, sx_tau_eq, sx_stable, sx_P_clique, sx_P_pw, ?_,
    sx_C_edge, fun t ht => sx_C_cover t (sx_clique_mem ht), ?_, ?_, sx_outside, ?_⟩
  · rw [sx_P_card, sx_pack_eq]
  · rw [sx_C_card, sx_tau_eq]
  · intro D hE hC hcard
    rw [sx_tau_eq] at hcard
    exact sx_unique D hE hC hcard
  · intro t ht
    exact sx_last t (sx_clique_mem ht)
