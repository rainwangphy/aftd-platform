import AFTD.Prelude

/-!
# fhs_min_gap

Topic: information   Node: 355cf09326a6

Provenance: formalization of a published result. Source: arXiv:2611.11747: Bounds and Constructions for Optimal Wide-Gap Frequency Hopping Sequences, Definition 1.1

The minimum gap of a frequency hopping sequence X : Fin v → Fin s of period v over alphabet size s is the minimum over all positions j of |X(j + 1) - X(j)| - 1, evaluated as integers.
-/

/-- The minimum gap of a frequency hopping sequence, defined as the minimum over all positions j of |X(j+1) - X(j)| - 1. -/
def fhs_min_gap {v s : ℕ} [NeZero v] (X : Fin v → Fin s) : ℤ := (Finset.univ.image (fun j : Fin v => |(X (j + 1) : ℤ) - (X j : ℤ)| - 1)).min'
  (Finset.Nonempty.image Finset.univ_nonempty _)
