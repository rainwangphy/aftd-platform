import AFTD.Prelude
import AFTD.Kb.Physics.OddRunAux

/-!
# odd_run_count

Topic: quantum_mechanics   Node: 9b8879d11859

Provenance: helper lemma. step towards claw_free_tree_graph_state_mmi

`odd_run_count l` is the number of maximal runs of `true` in the boolean word `l` whose length is odd. The final `false` is appended so that a trailing run is also completed.
-/

/-- Number of maximal odd-length runs of `true` in a boolean word. -/
def odd_run_count (l : List Bool) : ℕ := odd_run_aux false false (l ++ [false])
