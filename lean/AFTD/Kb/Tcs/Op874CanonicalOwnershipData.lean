import AFTD.Prelude

/-!
# op874_canonical_ownership_data

Topic: combinatorics   Node: 4811f44ebad6

Provenance: helper lemma. Modular separated-ownership obstruction, experiments 35686 and 35712.

The concrete map from fourteen three-position consumers to six seven-position producers plus one escape.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Canonical

def pick (t : Fin 14 → Fin 3) (i : Fin 14) : Fin 42 :=
  ⟨3*i.val + (t i).val, by have := i.isLt; have := (t i).isLt; omega⟩

def slot (k : Fin 42) : Option (Fin 6 × Fin 7) :=
  if k = 0 then none else
    some (⟨(5*k.val%42)/7, by have h := Nat.mod_lt (5*k.val) (by omega : 0<42); omega⟩,
          ⟨(5*k.val%42)%7, Nat.mod_lt _ (by omega)⟩)

end In1081Canonical

def op874_canonical_ownership_data : Fin 42 → Option (Fin 6 × Fin 7) := In1081Canonical.slot
