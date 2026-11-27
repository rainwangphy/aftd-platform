import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957FactorcriticalEndpointGroupParityBound
import AFTD.Kb.Tcs.OddGroupsSingleNonBlockComponentCount
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_factorcritical_single_exception_parity_bound

Topic: graphs   Node: 5bfb869bb7c1

Provenance: helper lemma. OP-1957: boundary minimum-degree reduction, arXiv:2611.22690

In the displayed factor-critical block with disjoint endpoint shores and odd anticomplete barrier groups, if the second shore meets the block and all barrier groups except one lie in the block, the displayed bound counts all groups and the parities of the outside pool and first-shore intersection.
-/

theorem op1957_factorcritical_single_exception_parity_bound
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
    (hYB : (Y ∩ B).Nonempty) (hoddT : ∀ i ∈ K, Odd (T i).card)
    (j : I) (hj : j ∈ K) (hother : ∀ i ∈ K, i ≠ j → T i ⊆ B) :
    let U := K.biUnion T
    let R := X ∪ Y ∪ U
    K.card + (if Even (U \ B).card then 1 else 0) +
      (if Odd ((X ∩ B).card) then 1 else 0) + (B ∩ R).card ≤ B.card + 1 := by
  classical
  dsimp only
  have hbound := op1957_factorcritical_endpoint_group_parity_bound G B X Y K T
    hcrit hXY hXT hYT hTT hantiXY hantiXT hantiYT hantiTT hYB
  have heq := odd_groups_single_non_block_component_count K T B j hj hTT hoddT hother
  dsimp only at hbound heq
  omega
