import AFTD.Prelude
import AFTD.Kb.Tcs.Op874DisjointMatchingPalettesCutData

/-!
# op874_disjoint_palette_cut_is_maximum

Topic: graphs   Node: 146c76de48aa

Provenance: helper lemma. Maximum-cut certificate for the matching-palette obstruction in OP-874; https://arxiv.org/abs/2610.41950.

The matching-constant cut used in the eight-vertex disjoint-palette obstruction is globally maximum for that matching: its eight-cycle has six crossing edges and no matching-constant bit assignment has more.
-/

theorem op874_disjoint_palette_cut_is_maximum :
    let mate : Fin 8 → Fin 8 := ![6,4,7,5,1,3,0,2]
    let bit : Fin 8 → Bool := ![true,false,false,true,false,true,true,false]
    (Finset.univ.filter fun v : Fin 8 => bit v ≠ bit (v+1)).card = 6 ∧
    (∀ b : Fin 8 → Bool, (∀ v, b v = b (mate v)) →
      (Finset.univ.filter fun v : Fin 8 => b v ≠ b (v+1)).card ≤ 6) := by
  decide
