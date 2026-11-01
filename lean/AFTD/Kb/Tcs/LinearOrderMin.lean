import AFTD.Prelude

/-!
# linearOrderMin

Topic: quantum   Node: 7f740e19e170

Provenance: formalization of a published result. Source: arXiv:2610.34762 Section 2

The minimum element of Fin n with respect to a linear order L, for n > 0.
-/

/-- The minimum element of `Fin n` with respect to a linear order `L`, for `0 < n`. -/
def linearOrderMin {n : ℕ} (hn : 0 < n) (L : LinearOrder (Fin n)) : Fin n :=
  @Finset.min' (Fin n) L Finset.univ
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
