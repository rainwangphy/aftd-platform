import AFTD.Prelude

/-!
# k_submod_join

Topic: submodular   Node: 6f73442d46a8

Provenance: formalization of a published result. Source: arXiv:2610.26677, line 98

Join of two assignments x and y in Fin n → Option (Fin k): at each coordinate e, if one is none it takes the other, if both agree it takes that value, and if they conflict it takes none.
-/

/-- Coordinatewise join of two assignments Fin n → Option (Fin k). -/
def k_submod_join {n k : ℕ} (x y : Fin n → Option (Fin k)) : Fin n → Option (Fin k) := fun e =>
    match x e, y e with
    | none, b => b
    | a, none => a
    | some i, some j => if i = j then some i else none
