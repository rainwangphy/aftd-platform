import AFTD.Prelude

/-!
# k_submod_meet

Topic: submodular   Node: 274d659089f7

Provenance: formalization of a published result. Source: arXiv:2610.26677, line 98

Meet of two assignments x and y in Fin n → Option (Fin k): at each coordinate e, it is x e if x e = y e, and none otherwise.
-/

/-- Coordinatewise meet of two assignments Fin n → Option (Fin k). -/
def k_submod_meet {n k : ℕ} (x y : Fin n → Option (Fin k)) : Fin n → Option (Fin k) := fun e =>
    match x e, y e with
    | some i, some j => if i = j then some i else none
    | _, _ => none
