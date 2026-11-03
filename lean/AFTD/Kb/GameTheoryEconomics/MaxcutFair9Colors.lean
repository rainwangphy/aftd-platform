import AFTD.Prelude

/-!
# maxcut_fair9_colors

Topic: equilibria   Node: 511e7db005e2

Provenance: helper lemma. Nine-vertex finite obstruction to fair Nash selection in the OP-85 strong-equilibrium campaign, discovered in experiment 12959 and independently checked in 12961, 12964, and 12973.

The nine-vertex three-color profile whose first color is zero and whose remaining colors are specified by eight arguments.
-/

def maxcut_fair9_colors (a b c d e f g h : Fin 3) : Fin 9 → Fin 3 := ![0,a,b,c,d,e,f,g,h]
