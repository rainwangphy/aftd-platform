import AFTD.Prelude

/-!
# hamming_weight

Topic: circuits   Node: 08815419fe0f

Provenance: formalization of a published result. Source: scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:713

The Hamming weight of a Boolean vector x is the number of true coordinates.
-/

/-- The Hamming weight of a Boolean vector x in {0,1}^n. -/
def hamming_weight {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card
