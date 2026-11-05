import AFTD.Prelude

/-!
# bicirculant_3465_column_cycle

Topic: graphs   Node: 19d9dec610b4

Provenance: helper lemma. step towards op_1151_bicirculant_3465_is_hamiltonian

An explicit closed-form Hamiltonian ordering of the 1155 columns (elements of ZMod 1155): i ↦ -387*(i/3) - (0 if i%3=0 else 35 if i%3=1 else 112). Successive values differ by one of -35, -77, -275, and all 1155 values are distinct.
-/

def bicirculant_3465_column_cycle (i : Fin 1155) : ZMod 1155 := -(((387 * (i.val / 3) : ℕ)) : ZMod 1155)
    - (if i.val % 3 = 0 then (0 : ZMod 1155) else if i.val % 3 = 1 then 35 else 112)
