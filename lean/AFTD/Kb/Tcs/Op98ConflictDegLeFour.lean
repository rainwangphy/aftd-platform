import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.IsSquareLocallyOptimal
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.ConflictNeighborhood
import AFTD.Kb.Tcs.Op98ConflictDegreeBound
import AFTD.Kb.Tcs.SquaredWeight

/-!
# op_98_conflict_deg_le_four

Topic: approximation   Node: a1d9b69c3785

Provenance: helper lemma. step towards op_98_repairs_free_bound

For any weighted 4-set packing instance inst and packings A, O, if A is square locally optimal and o ∈ O, then (conflict_neighborhood A {o}).card ≤ 4.
-/

/-- Every element o of a packing O has conflict degree at most 4 in A for a 4-set packing instance. -/
theorem op_98_conflict_deg_le_four {α : Type*} [DecidableEq α]
    (inst : WeightedSetPackingInstance α 4) (A O : Finset (Finset α))
    (hA : is_square_locally_optimal inst 4 A) (hO : is_packing inst O)
    (o : Finset α) (ho : o ∈ O) :
    (conflict_neighborhood A {o}).card ≤ 4 := by
  have hfs : conflict_neighborhood A {o} = A.filter (fun a => ¬ Disjoint o a) := by
    ext a
    simp [conflict_neighborhood, Finset.mem_singleton, disjoint_comm]
  rw [hfs]
  have h1 := op_98_conflict_degree_bound inst A o hA.1
  have h2 := inst.card_le o (hO.1 ho)
  omega
