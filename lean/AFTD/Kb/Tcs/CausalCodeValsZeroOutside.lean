import AFTD.Prelude
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.CapacitatedNetwork

/-!
# causal_code_vals_zero_outside

Topic: information   Node: 09ddca27f9b1

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

Let a causal linear code on net have transmission values val satisfying the recurrence for a message msg, where msg vanishes on sessions whose source is outside S and val vanishes on transmissions that leave S. Then val vanishes on every transmission whose receiver is outside S.
-/

/-- Values on a cut that carry no traffic vanish on the far side of the cut. -/
theorem causal_code_vals_zero_outside
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K)
    (code : CausalLinearNetworkCode V K F net sess) (S : Finset V) (msg : K → Fin code.L → F)
    (val : Fin code.M → F)
    (hval : ∀ m, val m = ∑ k, ∑ j, code.α m k j * msg k j + ∑ m', code.β m m' * val m')
    (hmsg : ∀ (k : K) (j : Fin code.L), sess.src k ∉ S → msg k j = 0)
    (hleave : ∀ m : Fin code.M, code.snd m ∈ S → code.rcv m ∉ S → val m = 0) :
    ∀ m : Fin code.M, code.rcv m ∉ S → val m = 0 := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
    intro hrcv
    by_cases hsnd : code.snd m ∈ S
    · exact hleave m hsnd hrcv
    · rw [hval m]
      have h1 : (∑ k, ∑ j, code.α m k j * msg k j) = (0 : F) := by
        apply Finset.sum_eq_zero
        intro k _
        apply Finset.sum_eq_zero
        intro j _
        by_cases hα : code.α m k j = 0
        · rw [hα, zero_mul]
        · have hsrc := code.snd_local m k j hα
          have hk : sess.src k ∉ S := by
            rw [hsrc]
            exact hsnd
          rw [hmsg k j hk, mul_zero]
      have h2 : (∑ m', code.β m m' * val m') = (0 : F) := by
        apply Finset.sum_eq_zero
        intro m' _
        by_cases hβ : code.β m m' = 0
        · rw [hβ, zero_mul]
        · have hlt : m' < m := code.causal m m' hβ
          have hrcv' : code.rcv m' = code.snd m := code.rcv_local m m' hβ
          have hrcv_not : code.rcv m' ∉ S := by
            rw [hrcv']
            exact hsnd
          have hval' : val m' = 0 := ih m' hlt hrcv_not
          rw [hval', mul_zero]
      rw [h1, h2, add_zero]
