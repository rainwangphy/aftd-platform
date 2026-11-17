import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForcingFinsetIterDecides
import AFTD.Kb.Tcs.ZeroForcingFinsetIter
import AFTD.Kb.Tcs.ZfsComplIffNoStuck
import AFTD.Kb.Tcs.IsZeroForcingSetMono
import AFTD.Kb.Tcs.ZeroForced
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# tree_zero_forcing_fixed_color_not_ultra_log_concave

Topic: graphs   Node: 52c51c8b0d90

Provenance: helper lemma.

There is a 14-vertex tree and a fixed-color restriction with five free vertices whose fort-free white ranks 1, 2, and 3 are 5, 6, and 4, violating normalized log-concavity.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IN919

def edges : List (Fin 14 × Fin 14) := [(1,0),(1,2),(1,7),(0,8),(2,3),(3,4),(4,5),(5,6),(8,9),(9,10),(10,11),(10,13),(11,12)]
def G : SimpleGraph (Fin 14) where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro v; fin_cases v <;> decide⟩
instance : DecidableRel G.Adj := by
  intro u v
  change Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges)
  infer_instance

lemma tree_zfc14_card : Nat.card ↑G.edgeSet + 1 = Nat.card (Fin 14) := by
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  decide

lemma tree_zfc14_connected : G.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  have e01 : G.Adj 0 1 := by decide
  have e12 : G.Adj 1 2 := by decide
  have e17 : G.Adj 1 7 := by decide
  have e08 : G.Adj 0 8 := by decide
  have e23 : G.Adj 2 3 := by decide
  have e34 : G.Adj 3 4 := by decide
  have e45 : G.Adj 4 5 := by decide
  have e56 : G.Adj 5 6 := by decide
  have e89 : G.Adj 8 9 := by decide
  have e910 : G.Adj 9 10 := by decide
  have e1011 : G.Adj 10 11 := by decide
  have e1013 : G.Adj 10 13 := by decide
  have e1112 : G.Adj 11 12 := by decide
  intro x
  fin_cases x
  · exact SimpleGraph.Reachable.rfl
  · exact e01.reachable
  · exact e01.reachable.trans e12.reachable
  · exact (e01.reachable.trans e12.reachable).trans e23.reachable
  · exact ((e01.reachable.trans e12.reachable).trans e23.reachable).trans e34.reachable
  · exact (((e01.reachable.trans e12.reachable).trans e23.reachable).trans e34.reachable).trans e45.reachable
  · exact ((((e01.reachable.trans e12.reachable).trans e23.reachable).trans e34.reachable).trans e45.reachable).trans e56.reachable
  · exact e01.reachable.trans e17.reachable
  · exact e08.reachable
  · exact e08.reachable.trans e89.reachable
  · exact (e08.reachable.trans e89.reachable).trans e910.reachable
  · exact ((e08.reachable.trans e89.reachable).trans e910.reachable).trans e1011.reachable
  · exact (((e08.reachable.trans e89.reachable).trans e910.reachable).trans e1011.reachable).trans e1112.reachable
  · exact ((e08.reachable.trans e89.reachable).trans e910.reachable).trans e1013.reachable

lemma tree_zfc14_isTree : G.IsTree :=
  SimpleGraph.isTree_iff_connected_and_card.mpr ⟨tree_zfc14_connected, tree_zfc14_card⟩

def pinned : Finset (Fin 14) := {1,3,6,7,8,10,12}
def freeMap : Fin 5 → Fin 14 := ![0,4,5,11,13]
def blue (S : Finset (Fin 5)) : Finset (Fin 14) := Finset.univ \ (pinned ∪ S.image freeMap)
def good (S : Finset (Fin 5)) : Prop := zero_forcing_finset_iter G (blue S) 14 = Finset.univ
instance (S : Finset (Fin 5)) : Decidable (good S) := by unfold good; infer_instance

def level (k : ℕ) : Finset (Finset (Fin 5)) := Finset.univ.filter (fun S => S.card = k ∧ good S)



theorem good_down {S T : Finset (Fin 5)} (h : S ⊆ T) (ht : good T) : good S := by
  apply (zero_forcing_finset_iter_decides G (blue S)).mp
  have hg := (zero_forcing_finset_iter_decides G (blue T)).mpr ht
  apply is_zero_forcing_set_mono G _ hg
  intro v hv
  simp only [blue, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_union] at hv ⊢
  intro hvS
  apply hv
  rcases hvS with ha | hs
  · exact Or.inl ha
  · exact Or.inr (Finset.image_subset_image h hs)

lemma tree_zfc14_step_zero_nbrs {S : Set (Fin 14)} (u w : Fin 14) (h : ∀ x, G.Adj u x → x ≠ w → False)
    (hu : ZeroForced G S u) (hadj : G.Adj u w) :
    ZeroForced G S w := by
  apply ZeroForced.step u w hu hadj
  intro x hx hne; exact (h x hx hne).elim

lemma tree_zfc14_step_one_nbr {S : Set (Fin 14)} (u w k : Fin 14) (h : ∀ x, G.Adj u x → x ≠ w → x = k)
    (hu : ZeroForced G S u) (hadj : G.Adj u w)
    (hk : ZeroForced G S k) :
    ZeroForced G S w := by
  apply ZeroForced.step u w hu hadj
  intro x hx hne; have : x = k := h x hx hne; subst this; exact hk

lemma tree_zfc14_step_two_nbrs {S : Set (Fin 14)} (u w k1 k2 : Fin 14) (h : ∀ x, G.Adj u x → x ≠ w → x = k1 ∨ x = k2)
    (hu : ZeroForced G S u) (hadj : G.Adj u w)
    (hk1 : ZeroForced G S k1) (hk2 : ZeroForced G S k2) :
    ZeroForced G S w := by
  apply ZeroForced.step u w hu hadj
  intro x hx hne; rcases h x hx hne with rfl | rfl <;> assumption

def tree_zfc14_A : Finset (Fin 14) := {1, 3, 6, 7, 8, 10, 12}
def tree_zfc14_B : Finset (Fin 14) := {0, 1, 3, 4, 5, 6, 7, 8, 10, 11, 12}
def tree_zfc14_x : Fin 14 := 13

def tree_zfc14_blue_b : Finset (Fin 14) := {2, 9, 13}

theorem tree_zfc14_blue_b_forcing : is_zero_forcing_set G (tree_zfc14_blue_b : Set (Fin 14)) := by
  have h2 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 2 := ZeroForced.init 2 (by decide)
  have h9 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 9 := ZeroForced.init 9 (by decide)
  have h13 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 13 := ZeroForced.init 13 (by decide)
  have h10 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 10 :=
    tree_zfc14_step_zero_nbrs 13 10 (by decide) h13 (by decide)
  have h8 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 8 :=
    tree_zfc14_step_one_nbr 9 8 10 (by decide) h9 (by decide) h10
  have h0 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 0 :=
    tree_zfc14_step_one_nbr 8 0 9 (by decide) h8 (by decide) h9
  have h1 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 1 :=
    tree_zfc14_step_one_nbr 0 1 8 (by decide) h0 (by decide) h8
  have h7 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 7 :=
    tree_zfc14_step_two_nbrs 1 7 0 2 (by decide) h1 (by decide) h0 h2
  have h3 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 3 :=
    tree_zfc14_step_one_nbr 2 3 1 (by decide) h2 (by decide) h1
  have h4 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 4 :=
    tree_zfc14_step_one_nbr 3 4 2 (by decide) h3 (by decide) h2
  have h5 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 5 :=
    tree_zfc14_step_one_nbr 4 5 3 (by decide) h4 (by decide) h3
  have h6 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 6 :=
    tree_zfc14_step_one_nbr 5 6 4 (by decide) h5 (by decide) h4
  have h11 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 11 :=
    tree_zfc14_step_two_nbrs 10 11 9 13 (by decide) h10 (by decide) h9 h13
  have h12 : ZeroForced G (tree_zfc14_blue_b : Set (Fin 14)) 12 :=
    tree_zfc14_step_one_nbr 11 12 10 (by decide) h11 (by decide) h10
  intro v; fin_cases v <;> assumption

def tree_zfc14_blue_ax : Finset (Fin 14) := {0, 2, 4, 5, 9, 11}

theorem tree_zfc14_blue_ax_forcing : is_zero_forcing_set G (tree_zfc14_blue_ax : Set (Fin 14)) := by
  have h0 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 0 := ZeroForced.init 0 (by decide)
  have h2 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 2 := ZeroForced.init 2 (by decide)
  have h4 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 4 := ZeroForced.init 4 (by decide)
  have h5 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 5 := ZeroForced.init 5 (by decide)
  have h9 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 9 := ZeroForced.init 9 (by decide)
  have h11 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 11 := ZeroForced.init 11 (by decide)
  have h3 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 3 :=
    tree_zfc14_step_one_nbr 4 3 5 (by decide) h4 (by decide) h5
  have h1 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 1 :=
    tree_zfc14_step_one_nbr 2 1 3 (by decide) h2 (by decide) h3
  have h8 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 8 :=
    tree_zfc14_step_one_nbr 0 8 1 (by decide) h0 (by decide) h1
  have h7 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 7 :=
    tree_zfc14_step_two_nbrs 1 7 0 2 (by decide) h1 (by decide) h0 h2
  have h6 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 6 :=
    tree_zfc14_step_one_nbr 5 6 4 (by decide) h5 (by decide) h4
  have h10 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 10 :=
    tree_zfc14_step_one_nbr 9 10 8 (by decide) h9 (by decide) h8
  have h13 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 13 :=
    tree_zfc14_step_two_nbrs 10 13 9 11 (by decide) h10 (by decide) h9 h11
  have h12 : ZeroForced G (tree_zfc14_blue_ax : Set (Fin 14)) 12 :=
    tree_zfc14_step_one_nbr 11 12 10 (by decide) h11 (by decide) h10
  intro v; fin_cases v <;> assumption

theorem good_four : good ({0,1,2,3} : Finset (Fin 5)) := by
  apply (zero_forcing_finset_iter_decides G (blue {0,1,2,3})).mp
  have h : blue ({0,1,2,3} : Finset (Fin 5)) = tree_zfc14_blue_b := by decide
  rw [h]
  exact tree_zfc14_blue_b_forcing

theorem good_one : good ({4} : Finset (Fin 5)) := by
  apply (zero_forcing_finset_iter_decides G (blue {4})).mp
  have h : blue ({4} : Finset (Fin 5)) = tree_zfc14_blue_ax := by decide
  rw [h]
  exact tree_zfc14_blue_ax_forcing

theorem bad0 : ¬ good ({0,4} : Finset (Fin 5)) := by
  intro h
  have hzf := (zero_forcing_finset_iter_decides G (blue {0,4})).mpr h
  change is_zero_forcing_set G ((Finset.univ \ (pinned ∪ ({0,4} : Finset (Fin 5)).image freeMap) : Finset (Fin 14)) : Set (Fin 14)) at hzf
  rw [zfs_compl_iff_no_stuck] at hzf
  apply hzf
  refine ⟨{0,7,8,10,12,13}, by decide, by decide, ?_⟩
  decide

theorem bad1 : ¬ good ({1,4} : Finset (Fin 5)) := by
  intro h
  have hzf := (zero_forcing_finset_iter_decides G (blue {1,4})).mpr h
  change is_zero_forcing_set G ((Finset.univ \ (pinned ∪ ({1,4} : Finset (Fin 5)).image freeMap) : Finset (Fin 14)) : Set (Fin 14)) at hzf
  rw [zfs_compl_iff_no_stuck] at hzf
  apply hzf
  refine ⟨{1,3,4,6,7,8,10,12,13}, by decide, by decide, ?_⟩
  decide

theorem bad2 : ¬ good ({2,4} : Finset (Fin 5)) := by
  intro h
  have hzf := (zero_forcing_finset_iter_decides G (blue {2,4})).mpr h
  change is_zero_forcing_set G ((Finset.univ \ (pinned ∪ ({2,4} : Finset (Fin 5)).image freeMap) : Finset (Fin 14)) : Set (Fin 14)) at hzf
  rw [zfs_compl_iff_no_stuck] at hzf
  apply hzf
  refine ⟨{1,3,5,6,7,8,10,12,13}, by decide, by decide, ?_⟩
  decide

theorem bad3 : ¬ good ({3,4} : Finset (Fin 5)) := by
  intro h
  have hzf := (zero_forcing_finset_iter_decides G (blue {3,4})).mpr h
  change is_zero_forcing_set G ((Finset.univ \ (pinned ∪ ({3,4} : Finset (Fin 5)).image freeMap) : Finset (Fin 14)) : Set (Fin 14)) at hzf
  rw [zfs_compl_iff_no_stuck] at hzf
  apply hzf
  refine ⟨{11,12,13}, by decide, by decide, ?_⟩
  decide

theorem good_iff (S : Finset (Fin 5)) : good S ↔ S ⊆ {0,1,2,3} ∨ S ⊆ {4} := by
  constructor
  · intro hs
    by_cases h4 : (4 : Fin 5) ∈ S
    · right
      intro v hv
      fin_cases v
      · exfalso; apply bad0; exact good_down (S := ({0,4} : Finset (Fin 5))) (T := S) (Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr h4⟩) hs
      · exfalso; apply bad1; exact good_down (S := ({1,4} : Finset (Fin 5))) (T := S) (Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr h4⟩) hs
      · exfalso; apply bad2; exact good_down (S := ({2,4} : Finset (Fin 5))) (T := S) (Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr h4⟩) hs
      · exfalso; apply bad3; exact good_down (S := ({3,4} : Finset (Fin 5))) (T := S) (Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr h4⟩) hs
      · simp
    · left
      intro v hv
      fin_cases v <;> simp_all
  · rintro (h | h)
    · exact good_down h good_four
    · exact good_down h good_one

theorem level_one : (level 1).card = 5 := by
  simp only [level, good_iff]
  decide

theorem level_two : (level 2).card = 6 := by
  simp only [level, good_iff]
  decide

theorem level_three : (level 3).card = 4 := by
  simp only [level, good_iff]
  decide


theorem count_eq (k : ℕ) :
    {S : Finset (Fin 5) | S.card = k ∧
      is_zero_forcing_set G ((Finset.univ \ (pinned ∪ S.image freeMap) : Finset (Fin 14)) : Set (Fin 14))}.ncard = (level k).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext S
  simp only [Set.mem_toFinset, Set.mem_setOf_eq, level, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [zero_forcing_finset_iter_decides]
  rfl


end IN919

theorem tree_zero_forcing_fixed_color_not_ultra_log_concave : ∃ (T : SimpleGraph (Fin 14))
    (A : Finset (Fin 14)) (f : Fin 5 → Fin 14), T.IsTree ∧ Function.Injective f ∧
    Disjoint A (Finset.univ.image f) ∧
    (let count := fun k : ℕ => {S : Finset (Fin 5) | S.card = k ∧
      is_zero_forcing_set T ((Finset.univ \ (A ∪ S.image f) : Finset (Fin 14)) : Set (Fin 14))}.ncard
     count 1 = 5 ∧ count 2 = 6 ∧ count 3 = 4) := by
  refine ⟨IN919.G, IN919.pinned, IN919.freeMap, IN919.tree_zfc14_isTree, ?_, ?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [IN919.freeMap]
  · decide
  · exact ⟨(IN919.count_eq 1).trans IN919.level_one, (IN919.count_eq 2).trans IN919.level_two,
      (IN919.count_eq 3).trans IN919.level_three⟩
