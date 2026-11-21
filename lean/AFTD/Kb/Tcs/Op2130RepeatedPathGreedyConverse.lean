import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130ConverseFromPathWitness
import AFTD.Kb.Tcs.Op2130PathCascadeWitness
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy
import AFTD.Kb.Tcs.CarpoolGreedyOrientations

/-!
# op_2130_repeated_path_greedy_converse

Topic: online_algorithms   Node: 8d418dd7ec90

Provenance: helper lemma. OP-2130: consequence of a successful path witness with at most D^3 requests; the related cubic-order path witness is Lemma 6 of https://drops.dagstuhl.de/storage/00lipics/lipics-vol055-icalp2016/LIPIcs.ICALP.2016.43/LIPIcs.ICALP.2016.43.pdf

There exists an absolute positive real constant C' such that for every integer D ≥ 1, there exists an edge sequence on the path graph SimpleGraph.pathGraph (2 * D) of length at most D^3 such that the uniform probability over all fair coin assignments that randomized greedy carpooling achieves maximum prefix discrepancy at least D is at least exp(-C' * D^3).
-/

/-- The converse in OP-2130: for every D ≥ 1, an oblivious edge sequence of at most D^3 requests on the 2D-vertex path graph achieves maximum prefix discrepancy D with probability at least exp(-C' * D^3). -/
theorem op_2130_repeated_path_greedy_converse :
    ∃ (C' : ℝ), 0 < C' ∧
      ∀ (D : ℕ) (hD : 1 ≤ D),
        ∃ (edges : List (Fin (2 * D) × Fin (2 * D))),
          (∀ e ∈ edges, (SimpleGraph.pathGraph (2 * D)).Adj e.1 e.2) ∧
          edges.length ≤ D ^ 3 ∧
          let T := edges.length
          let high_discrepancy := Finset.univ.filter (fun r : Fin T → Bool =>
            D ≤ carpool_max_discrepancy (2 * D) edges
              (carpool_greedy_orientations (2 * D) edges (List.ofFn r)))
          Real.exp (-C' * (D : ℝ) ^ 3) ≤ ((high_discrepancy.card : ℝ) / (2 ^ T : ℝ)) := by
  exact op_2130_converse_from_path_witness op_2130_path_cascade_witness
