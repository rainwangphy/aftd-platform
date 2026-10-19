import AFTD.Prelude

/-!
# css_z_distance_ge_three

Topic: quantum   Node: f0f7fed5d581

Provenance: formalization of a published result. Source: arXiv:2610.09341 Eq. 5

A CSS quantum code specified by a k by n logical X-operator matrix K and an s by n X-stabilizer matrix S over ZMod 2 has Z-distance at least 3 if every vector v in (ZMod 2)^n satisfying Sv = 0 and Kv ≠ 0 has Hamming weight at least 3.
-/

/-- A CSS code specified by a k x n logical X-matrix K and an s x n X-stabilizer matrix S has Z-distance at least 3. -/
def css_z_distance_ge_three {k s n : ℕ}
    (K : Matrix (Fin k) (Fin n) (ZMod 2)) (S : Matrix (Fin s) (Fin n) (ZMod 2)) : Prop :=
  ∀ v : Fin n → ZMod 2, Matrix.mulVec S v = 0 → Matrix.mulVec K v ≠ 0 →
    3 ≤ (Finset.univ.filter (fun j => v j ≠ 0)).card
