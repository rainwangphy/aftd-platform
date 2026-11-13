import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZfsComplIffNoStuck
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# tree_zf_white_rank_pair_positive_correlation

Topic: graphs   Node: fb03c7ddcf63

Provenance: helper lemma.

There is a six-vertex tree and two vertices such that, among the four-element white sets whose complements are zero forcing, the events that these vertices are white have positive correlation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace In800

def edges : List (Fin 6 × Fin 6) := [(0,1),(1,2),(0,3),(0,5),(3,4)]
def G : SimpleGraph (Fin 6) where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro v; fin_cases v <;> decide⟩
instance : DecidableRel G.Adj := by
  intro u v
  change Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges)
  infer_instance

def noFort (W : Finset (Fin 6)) : Prop :=
  ¬ ∃ fortSet : Finset (Fin 6), fortSet.Nonempty ∧ fortSet ⊆ W ∧
    ∀ u : Fin 6, u ∉ fortSet → ∀ w : Fin 6, w ∈ fortSet → G.Adj u w →
      ∃ x : Fin 6, x ∈ fortSet ∧ G.Adj u x ∧ x ≠ w
instance (W : Finset (Fin 6)) : Decidable (noFort W) := by
  unfold noFort
  infer_instance

theorem noFort_iff (W : Finset (Fin 6)) :
    noFort W ↔ is_zero_forcing_set G ((Finset.univ \ W : Finset (Fin 6)) : Set (Fin 6)) :=
  (zfs_compl_iff_no_stuck G W).symm

def level (k : ℕ) : Finset (Finset (Fin 6)) :=
  Finset.univ.filter fun W => W.card = k ∧ noFort W

theorem level_four : (level 4).card = 7 := by decide
theorem level_four_one : (level 4 |>.filter (fun W => (1 : Fin 6) ∈ W)).card = 5 := by decide
theorem level_four_four : (level 4 |>.filter (fun W => (4 : Fin 6) ∈ W)).card = 4 := by decide
theorem level_four_both : (level 4 |>.filter (fun W => (1 : Fin 6) ∈ W ∧ (4 : Fin 6) ∈ W)).card = 3 := by decide


theorem tree : G.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · apply (G.connected_iff_exists_forall_reachable).mpr
    refine ⟨0, ?_⟩
    have h01 : G.Reachable 0 1 := (show G.Adj 0 1 by decide).reachable
    have h02 : G.Reachable 0 2 := h01.trans (show G.Adj 1 2 by decide).reachable
    have h03 : G.Reachable 0 3 := (show G.Adj 0 3 by decide).reachable
    have h04 : G.Reachable 0 4 := h03.trans (show G.Adj 3 4 by decide).reachable
    have h05 : G.Reachable 0 5 := (show G.Adj 0 5 by decide).reachable
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.rfl
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h05
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide

def family : Set (Finset (Fin 6)) := {W | W.card = 4 ∧
  is_zero_forcing_set G ((Finset.univ \ W : Finset (Fin 6)) : Set (Fin 6))}

theorem family_count (P : Finset (Fin 6) → Prop) [DecidablePred P] :
    {W ∈ family | P W}.ncard = ((level 4).filter P).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext W
  simp [family, level, noFort_iff]

theorem total_count : family.ncard = 7 := by
  have h := family_count (fun _ => True)
  have hfamily : {W ∈ family | True} = family := by ext W; simp
  have hfilter : (level 4).filter (fun _ => True) = level 4 := by simp
  rw [hfamily, hfilter, level_four] at h
  exact h

theorem positive_corr :
    ∃ (T : SimpleGraph (Fin 6)) (i j : Fin 6), T.IsTree ∧ i ≠ j ∧
      (let fortSet : Set (Finset (Fin 6)) := {W | W.card = 4 ∧
        is_zero_forcing_set T ((Finset.univ \ W : Finset (Fin 6)) : Set (Fin 6))};
        {W ∈ fortSet | i ∈ W ∧ j ∈ W}.ncard * fortSet.ncard >
        {W ∈ fortSet | i ∈ W}.ncard * {W ∈ fortSet | j ∈ W}.ncard) := by
  refine ⟨G, 1, 4, tree, by decide, ?_⟩
  change {W ∈ family | (1 : Fin 6) ∈ W ∧ (4 : Fin 6) ∈ W}.ncard * family.ncard >
    {W ∈ family | (1 : Fin 6) ∈ W}.ncard * {W ∈ family | (4 : Fin 6) ∈ W}.ncard
  rw [family_count, family_count, family_count, total_count, level_four_both, level_four_one, level_four_four]
  decide

end In800

theorem tree_zf_white_rank_pair_positive_correlation : ∃ (T : SimpleGraph (Fin 6)) (i j : Fin 6), T.IsTree ∧ i ≠ j ∧ (let family : Set (Finset (Fin 6)) := {W | W.card = 4 ∧ is_zero_forcing_set T ((Finset.univ \ W : Finset (Fin 6)) : Set (Fin 6))}; {W ∈ family | i ∈ W ∧ j ∈ W}.ncard * family.ncard > {W ∈ family | i ∈ W}.ncard * {W ∈ family | j ∈ W}.ncard) := by
  exact In800.positive_corr
