import AFTD.Prelude
import AFTD.Kb.Tcs.IsSemistandard

/-!
# ssyt_bounded

Topic: combinatorics   Node: 3a9726e217e1

Provenance: formalization of a published result. Source: arXiv:2611.07715, Section 5.1

For a finite diagram D : Finset (ℕ × ℕ) and an integer bound m : ℕ, ssyt_bounded D m is the finite set of semi-standard fillings M : D → ℕ whose entries all lie in the interval {1, ..., m}.
-/

open Classical in
/-- The finite set of semi-standard Young tableaux of shape D with entries bounded by m. -/
noncomputable def ssyt_bounded (D : Finset (ℕ × ℕ)) (m : ℕ) : Finset (D → ℕ) := Finset.filter (fun M => is_semistandard D M)
    (Finset.image (fun (f : D → Finset.Icc 1 m) => fun u => (f u : ℕ)) Finset.univ)
