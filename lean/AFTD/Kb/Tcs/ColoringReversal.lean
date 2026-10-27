import AFTD.Prelude

/-!
# coloring_reversal

Topic: graphs   Node: b11ce595d84e

Provenance: formalization of a published result. Source: arXiv:2610.31785 Proposition 3.16 proof

For a proper coloring kappa : V -> Fin n of a simple graph G, the coloring obtained by mapping each color c to n - 1 - c is also a proper coloring.
-/

/-- The canonical color-reversing involution on proper n-colorings of a simple graph. -/
def coloring_reversal {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (κ : G.Coloring (Fin n)) : G.Coloring (Fin n) :=
  SimpleGraph.Coloring.mk (fun v => ⟨n - 1 - (κ v).val, by omega⟩) (by
    intro u v hadj h_eq
    have h_ne := κ.valid hadj
    apply h_ne
    ext
    have h_val := congrArg Fin.val h_eq
    dsimp at h_val
    omega)
