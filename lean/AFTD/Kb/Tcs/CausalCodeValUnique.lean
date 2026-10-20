import AFTD.Prelude
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.CapacitatedNetwork

/-!
# causal_code_val_unique

Topic: information   Node: 5d58686ae370

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

For a fixed message msg, any two assignments of transmission values satisfying the linear recurrence val m = sum alpha*msg + sum beta*val agree.
-/

/-- The transmission values of a causal linear code are uniquely determined by the message. -/
theorem causal_code_val_unique
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K)
    (code : CausalLinearNetworkCode V K F net sess) (msg : K → Fin code.L → F)
    (val val' : Fin code.M → F)
    (hval : ∀ m, val m = ∑ k, ∑ j, code.α m k j * msg k j + ∑ m', code.β m m' * val m')
    (hval' : ∀ m, val' m = ∑ k, ∑ j, code.α m k j * msg k j + ∑ m', code.β m m' * val' m') :
    val = val' := by
  ext m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
    rw [hval m, hval' m]
    congr 1
    apply Finset.sum_congr rfl
    intro m' _
    by_cases hβ : code.β m m' = 0
    · rw [hβ, zero_mul, zero_mul]
    · have hlt : m' < m := code.causal m m' hβ
      rw [ih m' hlt]
