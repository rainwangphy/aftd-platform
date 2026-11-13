import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZfsComplIffNoStuck
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.F

/-!
# tree_four_zf_white_rank_sequence_counterexample

Topic: graphs   Node: a739e5b2223f

Provenance: original. Related work: The tree zero forcing polynomial question is in https://arxiv.org/abs/2611.11352. Matroid independence-set ULC is proved in https://arxiv.org/abs/1811.01600.

There exists a four-vertex tree for which no matroid on its vertex set has the same numbers of independent sets of each size as the complements of zero forcing sets.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IN800PathMatroid

def edges : List (Fin 4 × Fin 4) := [(0,1),(1,2),(2,3)]
def G : SimpleGraph (Fin 4) where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro v; fin_cases v <;> decide⟩
instance : DecidableRel G.Adj := by
  intro u v
  change Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges)
  infer_instance

theorem tree : G.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · apply (G.connected_iff_exists_forall_reachable).mpr
    refine ⟨0, ?_⟩
    have h01 : G.Reachable 0 1 := (show G.Adj 0 1 by decide).reachable
    have h02 : G.Reachable 0 2 := h01.trans (show G.Adj 1 2 by decide).reachable
    have h03 : G.Reachable 0 3 := h02.trans (show G.Adj 2 3 by decide).reachable
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.rfl
    · exact h01
    · exact h02
    · exact h03
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide

def noFort (W : Finset (Fin 4)) : Prop :=
  ¬ ∃ F : Finset (Fin 4), F.Nonempty ∧ F ⊆ W ∧
    ∀ u : Fin 4, u ∉ F → ∀ w : Fin 4, w ∈ F → G.Adj u w →
      ∃ x : Fin 4, x ∈ F ∧ G.Adj u x ∧ x ≠ w
instance (W : Finset (Fin 4)) : Decidable (noFort W) := by
  unfold noFort
  infer_instance

theorem noFort_iff (W : Finset (Fin 4)) :
    noFort W ↔ is_zero_forcing_set G ((Finset.univ \ W : Finset (Fin 4)) : Set (Fin 4)) :=
  (zfs_compl_iff_no_stuck G W).symm

def level (k : ℕ) : Finset (Finset (Fin 4)) :=
  Finset.univ.filter fun W => W.card = k ∧ noFort W

theorem level_two : (level 2).card = 6 := by decide
theorem level_three : (level 3).card = 2 := by decide

theorem count_eq (k : ℕ) :
    {W : Finset (Fin 4) | W.card = k ∧
      is_zero_forcing_set G ((Finset.univ \ W : Finset (Fin 4)) : Set (Fin 4))}.ncard = (level k).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext W
  simp [level, noFort_iff]


-- A rank-three matroid on four vertices with all pairs independent cannot
-- have only two independent triples.
theorem no_matroid_two_triples (M : Matroid (Fin 4))
    (h2 : {W : Finset (Fin 4) | W.card = 2 ∧ M.Indep (W : Set (Fin 4))}.ncard = 6) :
    {W : Finset (Fin 4) | W.card = 3 ∧ M.Indep (W : Set (Fin 4))}.ncard ≠ 2 := by
  classical
  let pairs : Finset (Finset (Fin 4)) := Finset.univ.filter (fun W => W.card = 2)
  let goodPairs : Finset (Finset (Fin 4)) := pairs.filter (fun W => M.Indep (W : Set (Fin 4)))
  have hpairs : pairs.card = 6 := by decide
  have hgoodPairs : goodPairs.card = 6 := by
    rw [Set.ncard_eq_toFinset_card'] at h2
    convert h2 using 1 <;> simp [goodPairs, pairs, Finset.filter_filter]
  have heqPairs : goodPairs = pairs :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have allPairs (P : Finset (Fin 4)) (hP : P.card = 2) : M.Indep (P : Set (Fin 4)) := by
    have hmem : P ∈ pairs := by simp [pairs, hP]
    rw [← heqPairs] at hmem
    exact (Finset.mem_filter.mp hmem).2
  intro h3
  let triples : Finset (Finset (Fin 4)) :=
    Finset.univ.filter (fun W => W.card = 3 ∧ M.Indep (W : Set (Fin 4)))
  have hcard : triples.card = 2 := by
    rw [Set.ncard_eq_toFinset_card'] at h3
    convert h3 using 1 <;> simp [triples]
  obtain ⟨A, B, hAB, htriples⟩ := Finset.card_eq_two.mp hcard
  have hA : A ∈ triples := by rw [htriples]; simp
  have hB : B ∈ triples := by rw [htriples]; simp
  have hAprops := (Finset.mem_filter.mp hA).2
  have hBprops := (Finset.mem_filter.mp hB).2
  have hAc : (Finset.univ \ A).card = 1 := by simp [Finset.card_sdiff, hAprops.1]
  have hBc : (Finset.univ \ B).card = 1 := by simp [Finset.card_sdiff, hBprops.1]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hAc
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBc
  have haA : a ∉ A := by
    have : a ∈ Finset.univ \ A := by rw [ha]; simp
    exact (Finset.mem_sdiff.mp this).2
  have hbB : b ∉ B := by
    have : b ∈ Finset.univ \ B := by rw [hb]; simp
    exact (Finset.mem_sdiff.mp this).2
  have hab : a ≠ b := by
    intro h
    subst b
    have hc : Finset.univ \ A = Finset.univ \ B := ha.trans hb.symm
    apply hAB
    ext x
    have hx := congrArg (fun S : Finset (Fin 4) => x ∈ S) hc
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
    exact not_iff_not.mp (Iff.of_eq hx)
  let P : Finset (Fin 4) := {a, b}
  have hPc : P.card = 2 := by simp [P, hab]
  have hPi := allPairs P hPc
  obtain ⟨x, hxA, hxP, hxIndep⟩ := hPi.augment_finset hAprops.2 (by omega)
  have hD : insert x P ∈ triples := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, by simp [Finset.card_insert_of_notMem hxP, hPc], ?_⟩
    simpa only [Finset.coe_insert] using hxIndep
  rw [htriples] at hD
  simp only [Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with hD | hD
  · have : a ∈ A := by rw [← hD]; simp [P]
    exact haA this
  · have : b ∈ B := by rw [← hD]; simp [P]
    exact hbB this


theorem no_matching_matroid : ∃ T : SimpleGraph (Fin 4), T.IsTree ∧
    ∀ M : Matroid (Fin 4), ∃ k : ℕ,
      {W : Finset (Fin 4) | W.card = k ∧ M.Indep (W : Set (Fin 4))}.ncard ≠
      {W : Finset (Fin 4) | W.card = k ∧
        is_zero_forcing_set T ((Finset.univ \ W : Finset (Fin 4)) : Set (Fin 4))}.ncard := by
  refine ⟨G, tree, ?_⟩
  intro M
  by_contra h
  push_neg at h
  have h2 := h 2
  rw [count_eq, level_two] at h2
  have h3 := h 3
  rw [count_eq, level_three] at h3
  exact no_matroid_two_triples M h2 h3

end IN800PathMatroid

theorem tree_four_zf_white_rank_sequence_counterexample : ∃ T : SimpleGraph (Fin 4), T.IsTree ∧ ∀ M : Matroid (Fin 4), ∃ k : ℕ, {W : Finset (Fin 4) | W.card = k ∧ M.Indep (W : Set (Fin 4))}.ncard ≠ {W : Finset (Fin 4) | W.card = k ∧ is_zero_forcing_set T ((Finset.univ \ W : Finset (Fin 4)) : Set (Fin 4))}.ncard := by
  exact IN800PathMatroid.no_matching_matroid
