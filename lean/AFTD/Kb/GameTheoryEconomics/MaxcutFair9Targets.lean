import AFTD.Prelude

/-!
# maxcut_fair9_targets

Topic: equilibria   Node: b707aa1678d4

Provenance: helper lemma. Nine-vertex finite obstruction to fair Nash selection in the OP-85 strong-equilibrium campaign, discovered in experiment 12959 and independently checked in 12961, 12964, and 12973.

Six explicit three-color profiles used as finite deviation targets.
-/

def maxcut_fair9_targets : List (Fin 9 → Fin 3) :=
  let t1 : Fin 9 → Fin 3 := ![0,1,1,2,0,1,0,2,2]
  let t2 : Fin 9 → Fin 3 := ![0,1,1,2,1,2,0,2,0]
  let t3 : Fin 9 → Fin 3 := ![0,1,1,2,2,1,0,2,0]
  [t1, t2, t3,
   (fun v => Equiv.swap (1 : Fin 3) 2 (t1 v)),
   (fun v => Equiv.swap (1 : Fin 3) 2 (t2 v)),
   (fun v => Equiv.swap (1 : Fin 3) 2 (t3 v))]
