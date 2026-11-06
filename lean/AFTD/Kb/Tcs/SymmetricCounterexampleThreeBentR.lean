import AFTD.Prelude

/-!
# symmetric_counterexample_three_bent_r

Topic: combinatorics   Node: db5d741320ab

Provenance: formalization of a published result. Source: arXiv:2611.06744, Section 4

The Boolean function r on (Fin 4 → ZMod 2) taking the value 0 on {(1,0,0,1), (0,1,0,1), (1,1,1,1)} and 1 elsewhere.
-/

/-- The Boolean function r on (Fin 4 → ZMod 2) taking value 0 on {(1,0,0,1), (0,1,0,1), (1,1,1,1)} and 1 elsewhere. -/
def symmetric_counterexample_three_bent_r (X : Fin 4 → ZMod 2) : ZMod 2 :=
  let x0 := X 0; let x1 := X 1; let x2 := X 2; let x3 := X 3
  match x0.val, x1.val, x2.val, x3.val with
  | 1, 0, 0, 1 => 0
  | 0, 1, 0, 1 => 0
  | 1, 1, 1, 1 => 0
  | _, _, _, _ => 1
