import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenStripVertex

/-!
# petersen_strip_boundary

Topic: graphs   Node: 1a3f2b4594cb

Provenance: formalization of a published result. Source: scout/2610-24059-sharp-zero-forcing-numbers-for-the-generalized-petersen-gra.md:191

For a natural number k and a finite vertex set S : Finset PetersenStripVertex, `petersen_strip_boundary k S` is the `Finset PetersenStripVertex` defined by (S.biUnion N) \ S, where N (u i) = {u (i + 1), u (i - 1), v i} and N (v i) = if k = 0 then {u i} else {u i, v (i + k), v (i - k)}.
-/

/-- The external vertex boundary of a finite vertex set S in the generalized Petersen strip H_k. -/
def petersen_strip_boundary (k : ℕ) (S : Finset PetersenStripVertex) : Finset PetersenStripVertex :=
  (S.biUnion fun
    | .u i => { .u (i + 1), .u (i - 1), .v i }
    | .v i => if k = 0 then { .u i } else { .u i, .v (i + (k : ℤ)), .v (i - (k : ℤ)) }) \ S
