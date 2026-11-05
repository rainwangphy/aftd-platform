import AFTD.Prelude

/-!
# coord_shift_z

Topic: combinatorics   Node: f7d0e87ef10b

Provenance: formalization of a published result. Source: arXiv:2611.05261 equation (3)

For vectors x, y in (ZMod p)^d, the coordinate-shift vector z(x,y) has first coordinate x_0 + y_0 and j-th coordinate x_j + y_j + x_{j-1} * y_{j-1}^2 for j > 0.
-/

/-- Coordinate-shift map z(x,y) from dimension d to dimension d over ZMod p. -/
def coord_shift_z {p d : ℕ} (x y : Fin d → ZMod p) : Fin d → ZMod p := fun i =>
  if i.val = 0 then
    x i + y i
  else
    let prev : Fin d := ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
    x i + y i + x prev * (y prev) ^ 2
