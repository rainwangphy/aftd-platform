import AFTD.Prelude

/-!
# nat_mex_list

Topic: combinatorial_games   Node: d676907de24c

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md, Section 2.1

The minimum excluded value (mex) of a finite list of natural numbers is the least non-negative integer not in the list.
-/

/-- The minimum excluded value (mex) of a finite list of natural numbers. -/
def nat_mex_list (l : List ℕ) : ℕ :=
  let rec loop (n : ℕ) (fuel : ℕ) : ℕ :=
    match fuel with
    | 0 => n
    | fuel + 1 => if n ∈ l then loop (n + 1) fuel else n
  loop 0 (l.length + 1)
