import AFTD.Prelude

/-!
# odd_run_aux

Topic: quantum_mechanics   Node: 45ffbf757ed3

Provenance: helper lemma. step towards claw_free_tree_graph_state_mmi

`odd_run_aux inRun oddLen l` scans the boolean list `l` left to right, keeping a flag `inRun` (currently inside a run of `true`s) and `oddLen` (that run has odd length so far), and returns the number of completed runs of `true` of odd length.
-/

/-- Scanning accumulator counting completed odd-length runs of `true`. -/
def odd_run_aux : Bool → Bool → List Bool → ℕ := fun inRun oddLen l =>
  match l with
  | [] => 0
  | b :: t =>
      match b with
      | true => odd_run_aux true (cond inRun (Bool.not oddLen) true) t
      | false => (cond (inRun && oddLen) 1 0) + odd_run_aux false false t
