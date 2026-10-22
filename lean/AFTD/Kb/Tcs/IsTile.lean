import AFTD.Prelude

/-!
# IsTile

Topic: combinatorics   Node: b5de0fdd6f66

Provenance: formalization of a published result. Source: arXiv:2610.24022, Section 1

A subset E of F_2^d tiles F_2^d by translations if there exists a subset T of F_2^d such that E + T = F_2^d and |E| * |T| = 2^d.
-/

open scoped Pointwise in
/-- A subset E of F_2^d tiles F_2^d by translations if there exists a complement T such that E + T = univ and |E| * |T| = 2^d. -/
def IsTile {d : ℕ} (E : Finset (Fin d → ZMod 2)) : Prop := ∃ T : Finset (Fin d → ZMod 2), E + T = Finset.univ ∧ E.card * T.card = 2^d
