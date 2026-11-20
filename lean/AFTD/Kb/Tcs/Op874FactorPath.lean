import AFTD.Prelude

/-!
# op874_factor_path

Topic: graphs   Node: feaa7b6e2514

Provenance: helper lemma. Proper demand-covering factor paths for the OP-874 single-defect reduction.

A finite path of bounded four-color factor-edge values, each different from its predecessor, with each demand equal to one of its incident factor-edge values.
-/

namespace In1051Cert
inductive FactorPath (b : Nat) : List (Fin 4) → List Nat → Nat → Prop
  | base : FactorPath b [] [] b
  | extend {ds : List (Fin 4)} {cs : List Nat} {prev : Nat}
      (path : FactorPath b ds cs prev) (d : Fin 4) (c : Nat)
      (hproper : c ≠ prev) (hbound : c < 4) (hdemand : d.val = prev ∨ d.val = c) :
      FactorPath b (ds ++ [d]) (cs ++ [c]) c

end In1051Cert

def op874_factor_path (b : ℕ) (ds : List (Fin 4)) (cs : List ℕ) (last : ℕ) : Prop := In1051Cert.FactorPath b ds cs last
