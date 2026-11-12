import AFTD.Prelude
import AFTD.Kb.Tcs.GtsGraph
import AFTD.Kb.Tcs.Op223TreeAdjacentShiftOtherDegrees

/-!
# op223_tree_adjacent_shift_nonleaf_count

Topic: graphs   Node: 43f1fb5b4795

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; corrected versions of auxiliary statements retired by experiments 23031 and 23032

If both endpoints of an edge of a finite tree have degree at least two, shifting along that edge reduces the number of non-leaf vertices by exactly one.
-/

theorem op223_tree_adjacent_shift_nonleaf_count {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) (u v : V) (hT : T.IsTree) (huv : T.Adj u v) (hu : 2 ≤ Nat.card (T.neighborSet u)) (hv : 2 ≤ Nat.card (T.neighborSet v)) : (Finset.univ.filter (fun x : V => 1 < Nat.card ((gts_graph T u v u).neighborSet x))).card + 1 = (Finset.univ.filter (fun x : V => 1 < Nat.card (T.neighborSet x))).card := by
  classical
  -- After the shift, the candidate `v` has exactly one neighbour, namely `u`.
  have hvset : (gts_graph T u v u).neighborSet v = {u} := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, gts_graph, SimpleGraph.sup_adj,
      SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro (⟨hTx, hdel⟩ | ⟨⟨z, hz, hvz, hzu⟩, hvx⟩)
      · by_contra hxu
        apply hdel
        exact ⟨x, rfl, hTx, hxu⟩
      · rw [Sym2.eq_iff] at hz
        rcases hz with ⟨hvu, hxz⟩ | ⟨hvz', hxu⟩
        · exfalso; exact huv.ne hvu.symm
        · exfalso; exact hvz.ne hvz'
    · intro hxu
      subst hxu
      left
      constructor
      · exact huv.symm
      · rintro ⟨z, hz, hvz, hzu⟩
        rw [Sym2.eq_iff] at hz
        rcases hz with ⟨_, hxz⟩ | ⟨hvz', _⟩
        · exfalso; exact hzu hxz.symm
        · exfalso; exact hvz.ne hvz'
  have hv1 : Nat.card ((gts_graph T u v u).neighborSet v) = 1 := by
    rw [hvset]
    rw [show Nat.card ({u} : Set V) = ({u} : Set V).ncard from by
      rw [← Set.ncard_univ, Set.ncard_coe]]
    simp
  have hv_not : ¬ (1 < Nat.card ((gts_graph T u v u).neighborSet v)) := by omega
  -- The beneficiary `u` keeps at least the neighbours `v` and one further old neighbour.
  have hu_nonleaf : 1 < Nat.card ((gts_graph T u v u).neighborSet u) := by
    have hcard : 1 < Fintype.card (T.neighborSet u) := by
      rw [← Nat.card_eq_fintype_card]
      omega
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hcard
      ⟨v, (SimpleGraph.mem_neighborSet T u v).mpr huv⟩
    have hwv : b.1 ≠ v := fun h => hb (Subtype.ext h)
    have hadjuv : (gts_graph T u v u).Adj u v := by
      rw [gts_graph, SimpleGraph.sup_adj]
      left
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨huv, ?_⟩
      rintro ⟨z, hz, hvz, hzu⟩
      rw [Sym2.eq_iff] at hz
      rcases hz with ⟨huv', _⟩ | ⟨huz, _⟩
      · exact huv.ne huv'
      · exact hzu huz.symm
    have hadjuw : (gts_graph T u v u).Adj u b.1 := by
      rw [gts_graph, SimpleGraph.sup_adj]
      left
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨b.2, ?_⟩
      rintro ⟨z, hz, hvz, hzu⟩
      rw [Sym2.eq_iff] at hz
      rcases hz with ⟨huv', _⟩ | ⟨huz, hwv'⟩
      · exact huv.ne huv'
      · exact hwv hwv'
    have hpos : 1 < ((gts_graph T u v u).neighborSet u).ncard := by
      rw [Set.one_lt_ncard]
      exact ⟨v, (SimpleGraph.mem_neighborSet _ _ _).mpr hadjuv,
        b.1, (SimpleGraph.mem_neighborSet _ _ _).mpr hadjuw, fun h => hwv h.symm⟩
    have heq : Nat.card ((gts_graph T u v u).neighborSet u) =
        ((gts_graph T u v u).neighborSet u).ncard := by
      rw [← Set.ncard_univ, Set.ncard_coe]
    rw [heq]
    exact hpos
  -- Every vertex other than `v` has the same non-leaf status before and after.
  have hdegree : ∀ x : V, (x ≠ v → ((1 < Nat.card ((gts_graph T u v u).neighborSet x)) ↔
      (1 < Nat.card (T.neighborSet x)))) := by
    intro x hxv
    by_cases hxu : x = u
    · subst hxu
      constructor
      · exact fun _ => hu
      · exact fun _ => hu_nonleaf
    · rw [op223_tree_adjacent_shift_other_degrees T u v hT huv x hxu hxv]
  -- Hence the old non-leaves are exactly `v` together with the new non-leaves.
  have hfilter : (Finset.univ.filter (fun x : V => 1 < Nat.card (T.neighborSet x))) =
      insert v (Finset.univ.filter (fun x : V => 1 < Nat.card ((gts_graph T u v u).neighborSet x))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hx
      by_cases hxv : x = v
      · exact Or.inl hxv
      · exact Or.inr ((hdegree x hxv).mpr hx)
    · intro hx
      rcases hx with hxv | hx
      · subst hxv
        omega
      · by_cases hxv : x = v
        · subst hxv
          omega
        · exact (hdegree x hxv).mp hx
  have hmem : v ∉ Finset.univ.filter (fun x : V => 1 < Nat.card ((gts_graph T u v u).neighborSet x)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    omega
  rw [hfilter]
  rw [Finset.card_insert_of_notMem hmem]
