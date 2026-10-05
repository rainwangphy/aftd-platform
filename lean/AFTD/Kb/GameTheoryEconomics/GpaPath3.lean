import AFTD.Prelude

/-!
# gpa_path3

Topic: mechanism_design   Node: 16e6cbb868ad

The path 0 - 2 - 1 on three vertices.
-/

/-- The path `0 - 2 - 1` on three vertices. -/
def gpa_path3 : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2))

instance gpa_path3_adj_decidable : DecidableRel gpa_path3.Adj := by
  unfold gpa_path3
  infer_instance
