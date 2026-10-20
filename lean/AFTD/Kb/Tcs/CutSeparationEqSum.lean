import AFTD.Prelude
import AFTD.Kb.Tcs.CutSeparation
import AFTD.Kb.Tcs.UnicastSessions

/-!
# cutSeparation_eq_sum

Topic: information   Node: 16a1fa2cfb8c

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

Express cutSeparation as a sum of real indicator functions over sessions k in K.
-/

/-- Express cutSeparation as a sum of real indicator functions over sessions k in K. -/
theorem cutSeparation_eq_sum
    {V : Type} [DecidableEq V] {K : Type} [Fintype K]
    (sess : UnicastSessions V K) (S : Finset V) :
    (cutSeparation sess S : ℝ) =
      ∑ k : K, if (sess.src k ∈ S) ≠ (sess.tgt k ∈ S) then (1 : ℝ) else 0 := by
  simp only [cutSeparation]
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  simp
