import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_in693_ten_seed_packing_number

Topic: graphs   Node: bfbc57d0cb77

Provenance: helper lemma. Ten-vertex graph in experiment 20303. Kernel-checked finite maximum-packing computation; no novelty claim.

The concrete ten-vertex five-link seed has triangle packing number eight.
-/

open scoped Sym2

def in693_maxC {α : Type} (c : α → α → Bool) : ℕ → List α → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, t :: l => max (in693_maxC c n l) (1 + in693_maxC c n (l.filter (c t)))

theorem in693_maxC_bound {α : Type} [DecidableEq α] (c : α → α → Bool) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ S : Finset α, (∀ a ∈ S, a ∈ l) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → c a b = true) → S.card ≤ in693_maxC c n l := by
  intro n
  induction n with
  | zero =>
    intro l hl S hS _
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst hl0
    have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
    simp [this, in693_maxC]
  | succ n ih =>
    intro l hl S hS hc
    match l, hl, hS with
    | [], _, hS =>
      have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using hS a ha)
      simp [this, in693_maxC]
    | t :: l, hl, hS =>
      rw [in693_maxC]
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


def sharp_EL : List (Sym2 (Fin 10)) := [s(0,1), s(0,2), s(0,3), s(0,4), s(0,5), s(1,2), s(1,5), s(1,8), s(1,9), s(2,3), s(2,6), s(2,7), s(2,8), s(2,9), s(3,4), s(3,6), s(3,7), s(3,8), s(3,9), s(4,5), s(4,6), s(4,9), s(5,6), s(5,7), s(5,8), s(5,9), s(6,7), s(6,8), s(6,9), s(7,8), s(8,9)]
def sharp_T : List (Finset (Fin 10)) := [{0,1,2}, {0,1,5}, {0,2,3}, {0,3,4}, {0,4,5}, {1,2,8}, {1,2,9}, {1,5,8}, {1,5,9}, {1,8,9}, {2,3,6}, {2,3,7}, {2,3,8}, {2,3,9}, {2,6,7}, {2,6,8}, {2,6,9}, {2,7,8}, {2,8,9}, {3,4,6}, {3,4,9}, {3,6,7}, {3,6,8}, {3,6,9}, {3,7,8}, {3,8,9}, {4,5,6}, {4,5,9}, {4,6,9}, {5,6,7}, {5,6,8}, {5,6,9}, {5,7,8}, {5,8,9}, {6,7,8}, {6,8,9}]
def sharp_P : Finset (Finset (Fin 10)) := {{1,2,9}, {1,5,8}, {2,3,7}, {2,6,8}, {3,4,6}, {3,8,9}, {4,5,9}, {5,6,7}}
def sharp_E : Finset (Sym2 (Fin 10)) := sharp_EL.toFinset
def sharp_G : SimpleGraph (Fin 10) where
  Adj u v := s(u,v) ∈ sharp_E ∧ u ≠ v
  symm := ⟨fun u v h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩⟩
  loopless := ⟨fun u h => h.2 rfl⟩
instance : DecidableRel sharp_G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ sharp_E ∧ _ ≠ _))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem sharp_tri_complete : ∀ t ∈ (Finset.univ : Finset (Fin 10)).powersetCard 3,
    sharp_G.IsNClique 3 t → t ∈ sharp_T := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem sharp_T_clique : ∀ t ∈ sharp_T, sharp_G.IsNClique 3 t := by decide +kernel
lemma sharp_clique_mem {t : Finset (Fin 10)} (h : sharp_G.IsNClique 3 t) : t ∈ sharp_T :=
  sharp_tri_complete t (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h.card_eq⟩) h
def sharp_compat (s t : Finset (Fin 10)) : Bool := decide ((s ∩ t).card ≤ 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem sharp_maxC_eq : in693_maxC sharp_compat sharp_T.length sharp_T = 8 := by decide +kernel
lemma sharp_nu_le (T : Finset (Finset (Fin 10))) (hT : ∀ t ∈ T, sharp_G.IsNClique 3 t)
    (hP : (T : Set (Finset (Fin 10))).Pairwise (fun a b => (a ∩ b).card ≤ 1)) : T.card ≤ 8 :=
  calc T.card ≤ in693_maxC sharp_compat sharp_T.length sharp_T :=
        in693_maxC_bound sharp_compat _ sharp_T le_rfl T (fun a ha => sharp_clique_mem (hT a ha))
          (fun a ha b hb hab => decide_eq_true (hP (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab))
    _ = 8 := sharp_maxC_eq
theorem sharp_P_clique : ∀ t ∈ sharp_P, sharp_G.IsNClique 3 t := by decide +kernel
theorem sharp_P_pw : (sharp_P : Set (Finset (Fin 10))).Pairwise (fun a b => (a ∩ b).card ≤ 1) := by decide +kernel
theorem sharp_P_card : sharp_P.card = 8 := by decide +kernel
theorem sharp_pack_eq : simple_graph_triangle_packing_number sharp_G = 8 := by
  unfold simple_graph_triangle_packing_number
  refine IsGreatest.csSup_eq ⟨⟨sharp_P, sharp_P_clique, sharp_P_pw, sharp_P_card⟩, ?_⟩
  rintro n ⟨T, h1, h2, rfl⟩
  exact sharp_nu_le T h1 h2

theorem simple_graph_in693_ten_seed_packing_number : simple_graph_triangle_packing_number sharp_G = 8 := by
  exact sharp_pack_eq
