import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenStripVertex

/-!
# petersen_strip

Topic: graphs   Node: 2d718f4101d1

Provenance: formalization of a published result. Source: scout/2610-24059-sharp-zero-forcing-numbers-for-the-generalized-petersen-gra.md:140

For a natural number k, `petersen_strip k` is the infinite simple graph with vertex set `PetersenStripVertex` where vertices `u i` and `u j` are adjacent if `j = i + 1` or `j = i - 1`, `u i` and `v j` are adjacent if `j = i`, and `v i` and `v j` are adjacent if `k ≠ 0` and `j = i + k` or `j = i - k`.
-/

/-- The infinite generalized Petersen strip graph H_k with outer step 1, inner step k, and spokes. -/
def petersen_strip (k : ℕ) : SimpleGraph PetersenStripVertex where
  Adj x y := match x, y with
    | .u i, .u j => j = i + 1 ∨ j = i - 1
    | .u i, .v j => j = i
    | .v i, .u j => j = i
    | .v i, .v j => k ≠ 0 ∧ (j = i + (k : ℤ) ∨ j = i - (k : ℤ))
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> dsimp at h ⊢ <;> omega⟩
  loopless := ⟨by
    intro x h
    cases x <;> dsimp at h <;> omega⟩
