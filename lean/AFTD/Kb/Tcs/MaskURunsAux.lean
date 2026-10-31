import AFTD.Prelude

/-!
# mask_u_runs_aux

Topic: automata   Node: 632fc397a654

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 4

Auxiliary recursive function mask_u_runs_aux prev bs taking a previous boolean label prev and a list of booleans bs, returning the number of transitions from false to true in bs, where an empty list has 0 transitions, and a cons b :: bs adds 1 if prev is false and b is true, then recurses with prev replaced by b.
-/

/-- Auxiliary function to count maximal contiguous true runs in a binary list. -/
def mask_u_runs_aux (prev : Bool) : List Bool → ℕ
  | [] => 0
  | b :: bs => (if !prev && b then 1 else 0) + mask_u_runs_aux b bs
