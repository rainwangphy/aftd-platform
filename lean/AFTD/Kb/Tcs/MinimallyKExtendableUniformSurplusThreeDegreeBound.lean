import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.MinimallyKExtendableEvenJSurplusThreeDegreeBound
import AFTD.Kb.Tcs.MinimallyKExtendableOddJSurplusThreeDegreeBound

/-!
# minimally_k_extendable_uniform_surplus_three_degree_bound

Topic: graphs   Node: a74218247d91

Provenance: helper lemma. OP-1957: combine the even and odd surplus-three bounds. Not yet Lean-proved.

For j≥8 and j≤k, every minimally k-extendable graph on 2k+2j vertices has minimum degree at most 2k+j−4.
-/

theorem minimally_k_extendable_uniform_surplus_three_degree_bound
    (k j : ℕ) (hj : 8 ≤ j) (hjk : j ≤ k)
    (G : SimpleGraph (Fin (2*k+2*j))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) : G.minDegree ≤ 2*k+j-4 := by
  obtain heven | hodd := Nat.even_or_odd j
  · exact minimally_k_extendable_even_j_surplus_three_degree_bound k j hj heven hjk G hmin
  · obtain ⟨m, rfl⟩ := hodd
    have hj9 : 9 ≤ 2 * m + 1 := by omega
    exact minimally_k_extendable_odd_j_surplus_three_degree_bound k (2 * m + 1) hj9 ⟨m, rfl⟩ hjk G hmin
