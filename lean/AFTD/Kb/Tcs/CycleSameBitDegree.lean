import AFTD.Prelude

/-!
# cycle_same_bit_degree

Topic: graphs   Node: 83469883ccc2

Provenance: helper lemma. Local cycle/chord ownership construction for the OP-874 campaign.

The number of the two factor-cycle neighbors of a vertex having its bit.
-/

def cycle_same_bit_degree (n : ℕ) [NeZero n] (b : Fin n → Bool) (i : Fin n) : ℕ := (if b i = b (i-1) then 1 else 0) + (if b i = b (i+1) then 1 else 0)
