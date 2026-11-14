import AFTD.Prelude

/-!
# op861_ten_color_threefold_small_core

Topic: graphs   Node: a11d2a02b570

Provenance: helper lemma. Explicit finite obstruction for the k=7, r=3 subset graph of arXiv:2610.42094; extracted in experiments 26973 and 26975.

For every choice of the three non-forced right colors in the explicit ten-orbit instance, at least one of the four displayed left sets has every color forbidden by a right set meeting it in at most three elements.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def op861rot863 : Fin 13 → Fin 13 := ![1,2,0,4,5,3,7,8,6,10,11,9,12]
def op861pow863 (t : Fin 3) (x : Fin 13) : Fin 13 :=
  if t = 0 then x else if t = 1 then op861rot863 x else op861rot863 (op861rot863 x)
def op861left863 : Fin 4 → Finset (Fin 13) := ![
  {3,4,5,6,7,8,12}, {3,4,5,9,10,11,12},
  {3,4,6,9,10,11,12}, {6,7,8,9,10,11,12}]
def op861right863 : Fin 6 → Finset (Fin 13) := ![
  {0,1,2,3,4,5,9}, {0,1,2,3,4,5,12},
  {0,1,2,3,6,7,8}, {0,1,2,6,7,8,9},
  {0,1,2,6,7,8,12}, {0,1,2,9,10,11,12}]
def op861colors863 (a b c : Fin 4) : Fin 6 → Fin 13 := ![
  (![3,4,5,9] : Fin 4 → Fin 13) a, 12,
  (![3,6,7,8] : Fin 4 → Fin 13) b,
  (![6,7,8,9] : Fin 4 → Fin 13) c, 12, 12]

theorem op861_ten_color_threefold_small_core :
    ∀ a b c : Fin 4, ∃ i : Fin 4, ∀ x : Fin 13, x ∈ op861left863 i →
      ∃ j : Fin 6, ∃ t : Fin 3,
        ((op861left863 i) ∩ (op861right863 j).image (op861pow863 t)).card ≤ 3 ∧
        x = op861pow863 t (op861colors863 a b c j) := by
  decide
