import AFTD.Prelude

/-!
# k9_affine_triangle

Topic: graphs   Node: d422d2e88ae3

Provenance: formalization of a published result. Source: arXiv:2611.06362 Section 2.1

The monochromatic triangle `k9_affine_triangle` indexed by `color : Fin 4` and `line : ZMod 3`, defined as the finite set of vertices `p = (x, y) : ZMod 3 × ZMod 3` satisfying `x = line` for `color = 0`, `y = line` for `color = 1`, `y - x = line` for `color = 2`, and `y + x = line` for `color = 3`.
-/

/-- The monochromatic triangle in AG(2, 3) indexed by color (Fin 4) and line (ZMod 3). -/
def k9_affine_triangle (color : Fin 4) (line : ZMod 3) : Finset (ZMod 3 × ZMod 3) :=
  match color with
  | 0 => Finset.univ.filter (fun p => p.1 = line)
  | 1 => Finset.univ.filter (fun p => p.2 = line)
  | 2 => Finset.univ.filter (fun p => p.2 - p.1 = line)
  | 3 => Finset.univ.filter (fun p => p.2 + p.1 = line)
