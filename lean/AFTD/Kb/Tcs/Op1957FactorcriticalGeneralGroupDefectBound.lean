import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957FactorcriticalEndpointGroupParityBound
import AFTD.Kb.Tcs.Op1957OddGroupIntersectionDefectBound
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_factorcritical_general_group_defect_bound

Topic: graphs   Node: b0c411120c44

Provenance: helper lemma. OP-1957: one-defect boundary graph-to-count transfer, arXiv:2611.22690

Under the displayed factor-critical block and anticomplete shore hypotheses, the number of odd groups plus the first-shore odd indicator and occupied block vertices is at most the block size plus the pool vertices outside the block.
-/

theorem op1957_factorcritical_general_group_defect_bound
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B X Y : Finset V)
    (K : Finset I) (T : I → Finset V)
    (hcrit : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hXY : Disjoint X Y)
    (hXT : ∀ i ∈ K, Disjoint X (T i)) (hYT : ∀ i ∈ K, Disjoint Y (T i))
    (hTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (T i) (T j))
    (hantiXY : ∀ u ∈ X ∩ B, ∀ v ∈ Y ∩ B, ¬ G.Adj u v)
    (hantiXT : ∀ i ∈ K, ∀ u ∈ X, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiYT : ∀ i ∈ K, ∀ u ∈ Y, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, ¬ G.Adj u v)
    (hYB : (Y ∩ B).Nonempty) (hoddT : ∀ i ∈ K, Odd (T i).card) :
    let U := K.biUnion T
    let R := X ∪ Y ∪ U
    K.card + (if Odd ((X ∩ B).card) then 1 else 0) + (B ∩ R).card ≤ B.card + (U \ B).card := by
  classical
  dsimp only
  have hbound := op1957_factorcritical_endpoint_group_parity_bound G B X Y K T
    hcrit hXY hXT hYT hTT hantiXY hantiXT hantiYT hantiTT hYB
  have hcharge := op1957_odd_group_intersection_defect_bound B K T hTT hoddT
  dsimp only at hbound hcharge
  omega
