import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreClosedNeighborhoodBound
import AFTD.Kb.Physics.HardCoreVarSize

/-!
# op_1340_empty_graph_equality

Topic: statistical_mechanics   Node: b6fee681d4f7

Provenance: original. Related work: OP-1340; knowledgebase

On the empty (edgeless) graph (⊥ : SimpleGraph V) on a finite type V with decidable equality and positive vertex fugacities lam, hardCoreVarSize (⊥ : SimpleGraph V) lam is equal to hardCoreClosedNeighborhoodBound (⊥ : SimpleGraph V) lam.
-/

/-- Adding a vertex multiplies the partition function by `1 + lam a`. -/
private lemma op_1340_empty_graph_equality_P_insert {V : Type*} [DecidableEq V] (lam : V → ℝ)
    {a : V} {T : Finset V} (ha : a ∉ T) :
    (∑ I ∈ (insert a T).powerset, ∏ v ∈ I, lam v)
      = (1 + lam a) * ∑ I ∈ T.powerset, ∏ v ∈ I, lam v := by
  rw [Finset.sum_powerset_insert ha]
  have h2 : ∑ I ∈ T.powerset, (∏ v ∈ insert a I, lam v)
      = lam a * ∑ I ∈ T.powerset, ∏ v ∈ I, lam v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I hI => ?_
    have hai : a ∉ I := fun h => ha (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert hai]
  rw [h2]; ring

/-- Recurrence of the first moment sum when adding a vertex. -/
private lemma op_1340_empty_graph_equality_Q_insert {V : Type*} [DecidableEq V] (lam : V → ℝ)
    {a : V} {T : Finset V} (ha : a ∉ T) :
    (∑ I ∈ (insert a T).powerset, (∏ v ∈ I, lam v) * (I.card : ℝ))
      = (1 + lam a) * (∑ I ∈ T.powerset, (∏ v ∈ I, lam v) * (I.card : ℝ))
        + lam a * (∑ I ∈ T.powerset, ∏ v ∈ I, lam v) := by
  rw [Finset.sum_powerset_insert ha]
  have hB : ∑ I ∈ T.powerset, (∏ v ∈ insert a I, lam v) * ((insert a I).card : ℝ)
      = lam a * (∑ I ∈ T.powerset, (∏ v ∈ I, lam v) * (I.card : ℝ))
        + lam a * (∑ I ∈ T.powerset, ∏ v ∈ I, lam v) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I hI => ?_
    have hai : a ∉ I := fun h => ha (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert hai, Finset.card_insert_of_notMem hai]
    push_cast; ring
  rw [hB]; ring

/-- Recurrence of the second moment sum when adding a vertex. -/
private lemma op_1340_empty_graph_equality_R_insert {V : Type*} [DecidableEq V] (lam : V → ℝ)
    {a : V} {T : Finset V} (ha : a ∉ T) :
    (∑ I ∈ (insert a T).powerset, (∏ v ∈ I, lam v) * (I.card : ℝ)^2)
      = (1 + lam a) * (∑ I ∈ T.powerset, (∏ v ∈ I, lam v) * (I.card : ℝ)^2)
        + 2 * lam a * (∑ I ∈ T.powerset, (∏ v ∈ I, lam v) * (I.card : ℝ))
        + lam a * (∑ I ∈ T.powerset, ∏ v ∈ I, lam v) := by
  rw [Finset.sum_powerset_insert ha]
  have hB : ∑ I ∈ T.powerset, (∏ v ∈ insert a I, lam v) * ((insert a I).card : ℝ)^2
      = lam a * (∑ I ∈ T.powerset, (∏ v ∈ I, lam v) * (I.card : ℝ)^2)
        + 2 * lam a * (∑ I ∈ T.powerset, (∏ v ∈ I, lam v) * (I.card : ℝ))
        + lam a * (∑ I ∈ T.powerset, ∏ v ∈ I, lam v) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I hI => ?_
    have hai : a ∉ I := fun h => ha (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert hai, Finset.card_insert_of_notMem hai]
    push_cast; ring
  rw [hB]; ring

/-- The partition function of the hard-core model on an edgeless graph is positive. -/
private lemma op_1340_empty_graph_equality_P_pos {V : Type*} [DecidableEq V] (lam : V → ℝ)
    (hpos : ∀ v, 0 < lam v) (S : Finset V) :
    0 < ∑ I ∈ S.powerset, ∏ v ∈ I, lam v := by
  rw [← Finset.prod_add_one (f := lam) S]
  exact Finset.prod_pos fun i _ => by linarith [hpos i]

/-- The elementary algebra of the variance recursion under adding one vertex. -/
private lemma op_1340_empty_graph_equality_var_alg (P Q R w : ℝ) (hP : P ≠ 0) (h1 : 1 + w ≠ 0) :
    ((1 + w) * R + 2 * w * Q + w * P) / ((1 + w) * P)
      - (((1 + w) * Q + w * P) / ((1 + w) * P))^2
    = w / (1 + w)^2 + (R / P - (Q / P)^2) := by
  have hP1 : (1 + w) * P ≠ 0 := mul_ne_zero h1 hP
  field_simp
  ring

/-- For an edgeless graph on `S`, the variance of the independent-set size equals
`∑ v ∈ S, lam v / (1 + lam v)^2`. -/
private lemma op_1340_empty_graph_equality_var_finset {V : Type*} [DecidableEq V] (lam : V → ℝ)
    (hpos : ∀ v, 0 < lam v) (S : Finset V) :
    (∑ I ∈ S.powerset, (∏ v ∈ I, lam v) * (I.card : ℝ)^2) / (∑ I ∈ S.powerset, ∏ v ∈ I, lam v)
      - ((∑ I ∈ S.powerset, (∏ v ∈ I, lam v) * (I.card : ℝ)) / (∑ I ∈ S.powerset, ∏ v ∈ I, lam v))^2
    = ∑ v ∈ S, lam v / (1 + lam v)^2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [op_1340_empty_graph_equality_P_insert lam ha, op_1340_empty_graph_equality_Q_insert lam ha,
      op_1340_empty_graph_equality_R_insert lam ha, Finset.sum_insert ha, ← ih]
    have hP : (∑ I ∈ T.powerset, ∏ v ∈ I, lam v) ≠ 0 :=
      ne_of_gt (op_1340_empty_graph_equality_P_pos lam hpos T)
    have h1 : (1 + lam a) ≠ 0 := by linarith [hpos a]
    rw [op_1340_empty_graph_equality_var_alg _ _ _ _ hP h1]

/-- On an edgeless graph (empty graph), the hard-core variance of |I| equals the closed-neighborhood bound. -/
theorem op_1340_empty_graph_equality
    {V : Type*} [Fintype V] [DecidableEq V]
    (lam : V → ℝ) (hlam : ∀ v, 0 < lam v) :
    hardCoreVarSize (⊥ : SimpleGraph V) lam =
      hardCoreClosedNeighborhoodBound (⊥ : SimpleGraph V) lam := by
  have hfil : (Finset.univ.filter (fun I : Finset V => (⊥ : SimpleGraph V).IsIndepSet (↑I)))
      = Finset.univ := by
    rw [Finset.filter_true_of_mem]
    intro x _
    exact Set.pairwise_of_forall _ _ (fun a b => by simp)
  have hpu : (Finset.univ : Finset V).powerset = Finset.univ := Finset.powerset_univ
  have hvar : hardCoreVarSize (⊥ : SimpleGraph V) lam
      = (∑ I ∈ (Finset.univ : Finset V).powerset, (∏ v ∈ I, lam v) * (I.card : ℝ)^2)
          / (∑ I ∈ (Finset.univ : Finset V).powerset, ∏ v ∈ I, lam v)
        - ((∑ I ∈ (Finset.univ : Finset V).powerset, (∏ v ∈ I, lam v) * (I.card : ℝ))
            / (∑ I ∈ (Finset.univ : Finset V).powerset, ∏ v ∈ I, lam v))^2 := by
    simp only [hardCoreVarSize]
    rw [hfil, ← hpu]
  rw [hvar, op_1340_empty_graph_equality_var_finset lam hlam]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp
