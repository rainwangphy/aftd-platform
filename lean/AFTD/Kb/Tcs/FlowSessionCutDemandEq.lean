import AFTD.Prelude
import AFTD.Kb.Tcs.UnicastSessions

/-!
# flow_session_cut_demand_eq

Topic: information   Node: 6391a0137164

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

Summing the session demand indicators over a cut S yields r if src ∈ S and tgt ∉ S, -r if src ∉ S and tgt ∈ S, and 0 otherwise.
-/

/-- Summing the session demand indicators over a cut S yields r if src ∈ S and tgt ∉ S, -r if src ∉ S and tgt ∈ S, and 0 otherwise. -/
theorem flow_session_cut_demand_eq
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K]
    (sess : UnicastSessions V K) (r : ℝ) (k : K) (S : Finset V) :
    ∑ v ∈ S, (if v = sess.src k then r else if v = sess.tgt k then -r else 0) =
      if sess.src k ∈ S ∧ sess.tgt k ∉ S then r
      else if sess.src k ∉ S ∧ sess.tgt k ∈ S then -r
      else 0 := by
  have hsplit :
      (∑ v ∈ S, (if v = sess.src k then r else if v = sess.tgt k then -r else 0))
        = (∑ v ∈ S, (if v = sess.src k then r else 0))
          + (∑ v ∈ S, (if v = sess.tgt k then -r else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hvs : v = sess.src k
    · simp [hvs, sess.src_ne_tgt k]
    · simp [hvs]
  rw [hsplit, Finset.sum_ite_eq', Finset.sum_ite_eq']
  by_cases hsrc : sess.src k ∈ S <;> by_cases htgt : sess.tgt k ∈ S <;>
    simp [hsrc, htgt]
