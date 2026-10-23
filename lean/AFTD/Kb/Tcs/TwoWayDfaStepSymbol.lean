import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa
import AFTD.Kb.Tcs.TwoWayDfaStep

/-!
# two_way_dfa_step_symbol

Topic: automata   Node: 880119a4b3c9

Provenance: helper lemma. sanity lemma for two_way_dfa_step

Sanity: at position i+1 ≤ |w| a step reads w_i and moves to i+2 or i.
-/

theorem two_way_dfa_step_symbol {σ Q : Type*} (A : two_way_dfa σ Q) (w : List σ) (q : Q) (i : ℕ)
    (hi : i < w.length) :
    two_way_dfa_step A w (q, i + 1) =
      (A.δ q w[i]).map (fun r => (r.1, if r.2 then i + 2 else i)) := by
  have h1 : i ≠ w.length := hi.ne
  simp [two_way_dfa_step, h1, List.getElem?_eq_getElem hi]
