import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreWeightedVar
import AFTD.Kb.Physics.HardCoreWeightedClosedNeighborhoodBound

/-!
# op_1355_empty_graph_equality

Topic: statistical_mechanics   Node: b5ae41730991

Provenance: formalization of a published result. Source: OP-1355

On the edgeless graph (⊥ : SimpleGraph V) on a finite type V with decidable equality, for all positive vertex fugacities lam and all nonnegative observable weights a, the weighted hard-core variance hardCoreWeightedVar (⊥ : SimpleGraph V) lam a equals the weighted closed-neighborhood bound hardCoreWeightedClosedNeighborhoodBound (⊥ : SimpleGraph V) lam a.
-/

/-- On an edgeless graph all subsets occur, so the partition function is a full product. -/
private lemma op_1355_empty_graph_equality_Zsum {V : Type*} [DecidableEq V]
    (lam : V → ℝ) (T : Finset V) :
    (∑ I ∈ T.powerset, ∏ v ∈ I, lam v) = ∏ v ∈ T, (1 + lam v) :=
  (Finset.prod_one_add (f := lam) T).symm

/-- Recursion for the partition function when a vertex is adjoined to the ground set. -/
private lemma op_1355_empty_graph_equality_Z_insert {V : Type*} [DecidableEq V]
    (lam _w : V → ℝ) (b : V) (T : Finset V) (hb : b ∉ T) :
    (∑ I ∈ (insert b T).powerset, ∏ v ∈ I, lam v)
      = (1 + lam b) * ∑ I ∈ T.powerset, ∏ v ∈ I, lam v := by
  rw [Finset.sum_powerset_insert hb]
  have h2 : ∀ I ∈ T.powerset, (∏ v ∈ insert b I, lam v) = lam b * ∏ v ∈ I, lam v := by
    intro I hI
    have hbi : b ∉ I := fun h => hb (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert hbi]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Recursion for the first moment of the observable when a vertex is adjoined. -/
private lemma op_1355_empty_graph_equality_A_insert {V : Type*} [DecidableEq V]
    (lam w : V → ℝ) (b : V) (T : Finset V) (hb : b ∉ T) :
    (∑ I ∈ (insert b T).powerset, (∏ v ∈ I, lam v) * (∑ v ∈ I, w v))
      = (1 + lam b) * (∑ I ∈ T.powerset, (∏ v ∈ I, lam v) * (∑ v ∈ I, w v))
        + lam b * w b * (∑ I ∈ T.powerset, ∏ v ∈ I, lam v) := by
  rw [Finset.sum_powerset_insert hb]
  have h2 : ∀ I ∈ T.powerset,
      (∏ v ∈ insert b I, lam v) * (∑ v ∈ insert b I, w v)
        = lam b * ((∏ v ∈ I, lam v) * (∑ v ∈ I, w v))
          + (lam b * w b) * (∏ v ∈ I, lam v) := by
    intro I hI
    have hbi : b ∉ I := fun h => hb (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert hbi, Finset.sum_insert hbi]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Recursion for the second moment of the observable when a vertex is adjoined. -/
private lemma op_1355_empty_graph_equality_B_insert {V : Type*} [DecidableEq V]
    (lam w : V → ℝ) (b : V) (T : Finset V) (hb : b ∉ T) :
    (∑ I ∈ (insert b T).powerset, (∏ v ∈ I, lam v) * (∑ v ∈ I, w v) ^ 2)
      = (1 + lam b) * (∑ I ∈ T.powerset, (∏ v ∈ I, lam v) * (∑ v ∈ I, w v) ^ 2)
        + 2 * lam b * w b * (∑ I ∈ T.powerset, (∏ v ∈ I, lam v) * (∑ v ∈ I, w v))
        + lam b * (w b) ^ 2 * (∑ I ∈ T.powerset, ∏ v ∈ I, lam v) := by
  rw [Finset.sum_powerset_insert hb]
  have h2 : ∀ I ∈ T.powerset,
      (∏ v ∈ insert b I, lam v) * (∑ v ∈ insert b I, w v) ^ 2
        = lam b * ((∏ v ∈ I, lam v) * (∑ v ∈ I, w v) ^ 2)
          + (2 * lam b * w b) * ((∏ v ∈ I, lam v) * (∑ v ∈ I, w v))
          + (lam b * (w b) ^ 2) * (∏ v ∈ I, lam v) := by
    intro I hI
    have hbi : b ∉ I := fun h => hb (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert hbi, Finset.sum_insert hbi]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The weighted hard-core variance over the full power set of `S` is the sum of the
per-vertex Bernoulli variances. -/
private lemma op_1355_empty_graph_equality_var_finset {V : Type*} [DecidableEq V]
    (lam w : V → ℝ) (hlam : ∀ v, 0 < lam v) (S : Finset V) :
    (∑ I ∈ S.powerset, (∏ v ∈ I, lam v) * (∑ v ∈ I, w v) ^ 2)
        / (∑ I ∈ S.powerset, ∏ v ∈ I, lam v)
      - ((∑ I ∈ S.powerset, (∏ v ∈ I, lam v) * (∑ v ∈ I, w v))
          / (∑ I ∈ S.powerset, ∏ v ∈ I, lam v)) ^ 2
    = ∑ v ∈ S, w v ^ 2 * lam v / (1 + lam v) ^ 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert b T hb ih =>
    rw [op_1355_empty_graph_equality_B_insert lam w b T hb,
      op_1355_empty_graph_equality_A_insert lam w b T hb,
      op_1355_empty_graph_equality_Z_insert lam w b T hb,
      Finset.sum_insert hb, ← ih]
    have hZ : (∑ I ∈ T.powerset, ∏ v ∈ I, lam v) ≠ 0 := by
      rw [op_1355_empty_graph_equality_Zsum lam T]
      exact ne_of_gt (Finset.prod_pos (fun v _ => by linarith [hlam v]))
    have hu : (1 + lam b) ≠ 0 := by linarith [hlam b]
    field_simp
    ring

/-- On an edgeless graph, the weighted hard-core variance equals the weighted closed-neighborhood bound. -/
theorem op_1355_empty_graph_equality
    {V : Type*} [Fintype V] [DecidableEq V]
    (lam : V → ℝ) (hlam : ∀ v, 0 < lam v) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    hardCoreWeightedVar (⊥ : SimpleGraph V) lam a =
      hardCoreWeightedClosedNeighborhoodBound (⊥ : SimpleGraph V) lam a := by
  have hfil : (Finset.univ.filter (fun I : Finset V => (⊥ : SimpleGraph V).IsIndepSet (↑I)))
      = Finset.univ := by
    rw [Finset.filter_true_of_mem]
    intro x _
    exact Set.pairwise_of_forall _ _ (fun a b => by simp)
  have hpu : (Finset.univ : Finset V).powerset = Finset.univ := Finset.powerset_univ
  have hvar : hardCoreWeightedVar (⊥ : SimpleGraph V) lam a
      = (∑ I ∈ (Finset.univ : Finset V).powerset,
            (∏ v ∈ I, lam v) * (∑ v ∈ I, a v) ^ 2)
          / (∑ I ∈ (Finset.univ : Finset V).powerset, ∏ v ∈ I, lam v)
        - ((∑ I ∈ (Finset.univ : Finset V).powerset, (∏ v ∈ I, lam v) * (∑ v ∈ I, a v))
            / (∑ I ∈ (Finset.univ : Finset V).powerset, ∏ v ∈ I, lam v)) ^ 2 := by
    simp only [hardCoreWeightedVar]
    rw [hfil, ← hpu]
  have hbound : hardCoreWeightedClosedNeighborhoodBound (⊥ : SimpleGraph V) lam a
      = ∑ v ∈ (Finset.univ : Finset V), a v ^ 2 * lam v / (1 + lam v) ^ 2 := by
    simp only [hardCoreWeightedClosedNeighborhoodBound]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp
  rw [hvar, hbound, op_1355_empty_graph_equality_var_finset lam a hlam Finset.univ]
