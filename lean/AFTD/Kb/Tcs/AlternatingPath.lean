import AFTD.Prelude
import AFTD.Kb.Tcs.AlternatingPathVertex

/-!
# alternating_path

Topic: graphs   Node: 06a1a876c323

Provenance: formalization of a published result. Source: arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 1

The alternating path AP_n is the ordered simple graph on Fin n whose edges connect consecutive vertices in the alternating sequence 0, n-1, 1, n-2, ....
-/

/-- The alternating path AP_n on Fin n whose vertices in path order alternate from the ends inward. -/
def alternating_path (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun a b =>
    ∃ m : ℕ, m + 1 < n ∧ a.val = alternating_path_vertex n m ∧ b.val = alternating_path_vertex n (m + 1))
