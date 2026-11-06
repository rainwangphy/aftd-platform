import AFTD.Prelude

/-!
# maxcut_unsafe_pivot_stable_profile

Topic: equilibria   Node: a8605152d01a

Provenance: helper lemma.

The three-color profile of the stable extension with an unsafe pivot.
-/

def maxcut_unsafe_pivot_stable_profile : Fin 6 → Fin 3 := ![0, 1, 2, 0, 0, 1]
