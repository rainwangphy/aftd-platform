import AFTD.Prelude

/-!
# ternary_single_point_repair

Topic: combinatorics   Node: f1936aa93cc5

Provenance: formalization of a published result. Source: arXiv:2610.32789, Section 3.1

Given an explicit natural number n, a finite set H : Finset (Fin n → ZMod 3), a point p : Fin n → ZMod 3, and an offset vector ε : Fin n → ZMod 3, the single-point repair of H at p by ε is the finite set (Finset) of vectors obtained by erasing p from H and taking the union with the image over all i : Fin n of Function.update p i (p i + ε i).
-/

/-- Single-point repair of H at p by replacing p with p + epsilon_i * e_i for each coordinate. -/
def ternary_single_point_repair (n : ℕ) (H : Finset (Fin n → ZMod 3)) (p : Fin n → ZMod 3) (ε : Fin n → ZMod 3) : Finset (Fin n → ZMod 3) := (H.erase p) ∪ (Finset.image (fun i => Function.update p i (p i + ε i)) Finset.univ)
