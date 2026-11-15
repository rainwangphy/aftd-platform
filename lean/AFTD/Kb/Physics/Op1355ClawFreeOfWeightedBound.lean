import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreWeightedVar
import AFTD.Kb.Physics.HardCoreWeightedClosedNeighborhoodBound
import AFTD.Kb.Tcs.IsClawFree
import AFTD.Kb.Physics.Op1355IndependentTriplePartitionLowerBound
import AFTD.Kb.Physics.Op1355ClawCenterPartitionUpperBound
import AFTD.Kb.Physics.Op1355ClawNeighborhoodSumUpperBound
import AFTD.Kb.Physics.Op1355CenterViolationOfPartitionBounds

/-!
# op_1355_claw_free_of_weighted_bound

Topic: statistical_mechanics   Node: 8466117d6305

Provenance: formalization of a published result. Source: OP-1355

If a finite simple graph G on a finite type V with decidable equality satisfies the weighted hard-core closed-neighborhood variance bound hardCoreWeightedClosedNeighborhoodBound G lam a ≤ hardCoreWeightedVar G lam a for all positive vertex fugacities lam and all nonnegative observable weights a, then G is claw-free.
-/

theorem op1355_not_claw_free_quadruple_scratch {V : Type*} (G : SimpleGraph V)
    (h : ¬ IsClawFree G) :
    ∃ c u v w : V, (G.Adj c u ∧ G.Adj c v ∧ G.Adj c w) ∧
      (u ≠ v ∧ u ≠ w ∧ v ≠ w) ∧
      (¬ G.Adj u v ∧ ¬ G.Adj u w ∧ ¬ G.Adj v w) := by
  classical
  have hex : SimpleGraph.IsIndContained (completeBipartiteGraph (Fin 1) (Fin 3)) G := by
    simpa [IsClawFree] using h
  obtain ⟨f⟩ := hex
  let c := f (Sum.inl (0 : Fin 1))
  let u := f (Sum.inr (0 : Fin 3))
  let v := f (Sum.inr (1 : Fin 3))
  let w := f (Sum.inr (2 : Fin 3))
  have huv : u ≠ v := by
    intro hh
    have hi := f.injective hh
    have hv := congrArg (fun z : Fin 1 ⊕ Fin 3 => match z with | Sum.inl _ => 99 | Sum.inr k => k.val) hi
    norm_num at hv
  have huw : u ≠ w := by
    intro hh
    have hi := f.injective hh
    have hv := congrArg (fun z : Fin 1 ⊕ Fin 3 => match z with | Sum.inl _ => 99 | Sum.inr k => k.val) hi
    norm_num at hv
  have hvw : v ≠ w := by
    intro hh
    have hi := f.injective hh
    have hv := congrArg (fun z : Fin 1 ⊕ Fin 3 => match z with | Sum.inl _ => 99 | Sum.inr k => k.val) hi
    norm_num at hv
  refine ⟨c,u,v,w, ⟨?_,?_,?_⟩, ⟨huv,huw,hvw⟩, ⟨?_,?_,?_⟩⟩
  all_goals dsimp only [c, u, v, w]
  all_goals rw [f.map_rel_iff]
  all_goals simp [completeBipartiteGraph]

/-- Graphs satisfying the weighted hard-core closed-neighborhood variance bound for all positive activities and nonnegative weights are claw-free. -/
theorem op_1355_claw_free_of_weighted_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbound : ∀ (lam : V → ℝ) (hlam : ∀ v, 0 < lam v) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v),
      hardCoreWeightedClosedNeighborhoodBound G lam a ≤ hardCoreWeightedVar G lam a) :
    IsClawFree G := by
  classical
  by_contra h
  obtain ⟨c,u,v,w,hadj,hdist,hnon⟩ := op1355_not_claw_free_quadruple_scratch G h
  let eps : ℝ := 1 / (16 * (2:ℝ)^Fintype.card V)
  have heps : 0 < eps := by dsimp [eps]; positivity
  let lam : V → ℝ := fun x => if x=c then 1 else if x=u ∨ x=v ∨ x=w then 10 else eps
  have hlamdef : ∀ x, lam x = if x=c then 1 else if x=u ∨ x=v ∨ x=w then 10 else 1 / (16 * (2:ℝ)^Fintype.card V) := by intro x; rfl
  have hpos : ∀ x, 0 < lam x := by
    intro x
    dsimp only [lam]
    split_ifs <;> positivity
  have hc : lam c = 1 := by simp [lam]
  have hu : lam u = 10 := by simp [lam, hadj.1.ne']
  have hv : lam v = 10 := by simp [lam, hadj.2.1.ne']
  have hw : lam w = 10 := by simp [lam, hadj.2.2.ne']
  have hZ := op_1355_independent_triple_partition_lower_bound G u v w hdist hnon lam (fun x => le_of_lt (hpos x)) ⟨hu,hv,hw⟩
  have hPmax := op_1355_claw_center_partition_upper_bound G c u v w hadj hdist hnon lam hlamdef
  have hP : 0 ≤ ∑ I ∈ (Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V) ∧ c ∈ I), ∏ x ∈ I, lam x := by
    exact Finset.sum_nonneg fun I _ => Finset.prod_nonneg fun x _ => le_of_lt (hpos x)
  have hD : 0 < 1 + ∑ x ∈ insert c (G.neighborFinset c), lam x := by
    have hs : 0 ≤ ∑ x ∈ insert c (G.neighborFinset c), lam x := Finset.sum_nonneg fun x _ => le_of_lt (hpos x)
    linarith
  have hDmax : 1 + (∑ x ∈ insert c (G.neighborFinset c), lam x) ≤ 33 := by
    have hN := op_1355_claw_neighborhood_sum_upper_bound G c u v w hadj hdist hnon lam hlamdef
    linarith
  have hviol := op_1355_center_violation_of_partition_bounds G lam c hc hZ hP hPmax hD hDmax
  have ha : ∀ x, 0 ≤ (if x = c then (1:ℝ) else 0) := by intro x; split_ifs <;> norm_num
  exact (not_lt_of_ge (hbound lam hpos _ ha)) hviol
