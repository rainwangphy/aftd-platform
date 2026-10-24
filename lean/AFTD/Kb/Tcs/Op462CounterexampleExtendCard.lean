import AFTD.Prelude
import AFTD.Kb.Tcs.GaleDistanceGraph
import AFTD.Kb.Tcs.GaleSigmaThree
import AFTD.Kb.Tcs.IsGaleCounterexampleThree

/-!
# op462_counterexample_extend_card

Topic: combinatorics   Node: 6ae3f112e273

Provenance: helper lemma. Helper for arXiv:2610.28828, Theorem 2. Reuses the exact coordinate and coloring certificates recorded in experiments 4045 and 4047; convex hull padding is elementary.

A finite three-dimensional counterexample can be enlarged to any prescribed larger finite cardinality by adding points inside its convex hull.
-/

theorem op462_counterexample_extend_card (V : Finset (EuclideanSpace ℝ (Fin 3))) (hV : is_gale_counterexample_three V)
    (n : ℕ) (hn : V.card ≤ n) :
    ∃ W : Finset (EuclideanSpace ℝ (Fin 3)), W.card = n ∧ is_gale_counterexample_three W := by
  classical
  have hnontriv : (V : Set (EuclideanSpace ℝ (Fin 3))).Nontrivial :=
    Set.not_subsingleton_iff.mp (fun hs => hV.1.ne' (Metric.diam_subsingleton hs))
  have hinf : (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 3)))).Infinite :=
    (convex_convexHull ℝ _).isPreconnected.infinite_of_nontrivial
      (hnontriv.mono (subset_convexHull ℝ _))
  obtain ⟨U, hU, hcardU⟩ := (hinf.sdiff V.finite_toSet).exists_subset_card_eq (n - V.card)
  have hdisj : Disjoint V U := by
    rw [Finset.disjoint_left]
    intro x hxV hxU
    exact (hU hxU).2 hxV
  have hsub : ((V ∪ U : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact subset_convexHull ℝ _ hx
    · exact (hU hx).1
  have hdiam : Metric.diam ((V ∪ U : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) =
      Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))) := by
    apply le_antisymm
    · exact (Metric.diam_mono hsub (isBounded_convexHull.mpr V.finite_toSet.isBounded)).trans_eq
        (convexHull_diam _)
    · exact Metric.diam_mono (by intro x hx; exact Finset.mem_union_left U hx)
        (V ∪ U).finite_toSet.isBounded
  refine ⟨V ∪ U, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hcardU, Nat.add_sub_of_le hn]
  · refine ⟨by simpa only [hdiam] using hV.1, ?_⟩
    rintro ⟨c⟩
    apply hV.2
    refine ⟨SimpleGraph.Coloring.mk (fun x => c ⟨x.val, Finset.mem_union_left U x.property⟩) ?_⟩
    intro x y hxy
    apply c.valid
    change (⟨x.val, Finset.mem_union_left U x.property⟩ : ↥(V ∪ U)) ≠
      ⟨y.val, Finset.mem_union_left U y.property⟩ ∧ _
    constructor
    · intro heq
      exact hxy.1 (Subtype.ext (congrArg (fun z : ↥(V ∪ U) => z.val) heq))
    · simpa only [hdiam] using hxy.2
