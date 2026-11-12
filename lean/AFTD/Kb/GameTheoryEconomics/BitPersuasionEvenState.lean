import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenCoord

/-!
# bit_persuasion_even_state

Topic: mechanism_design   Node: 4f4af0c29600

Provenance: formalization of a published result. Source: arXiv:2606.22226

The bit-vector state corresponding to s ∈ Fin (2m) in the two-layer construction, where coordinate c is 1 if and only if s is an element of the indexing subset of c.
-/

open Finset in
/-- State s of the two-layer construction: coordinate c is 1 iff s belongs to the indexing subset of c. -/
def bit_persuasion_even_state (m : ℕ) (s : Fin (2 * m)) : bit_persuasion_even_coord m → Bool :=
  fun c => match c with
  | Sum.inl (A, _) => decide (s ∈ A.1)
  | Sum.inr (B, _) => decide (s ∈ B.1)
