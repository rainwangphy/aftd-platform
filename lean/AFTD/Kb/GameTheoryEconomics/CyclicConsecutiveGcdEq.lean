import AFTD.Prelude

/-!
# cyclic_consecutive_gcd_eq

Topic: matching_markets   Node: dd810b9f8b95

Provenance: formalization of a published result. Source: OP-1351

Two ordering bijections a and b from Fin n to ZMod n satisfy cyclic_consecutive_gcd_eq a b if for every natural number r with r + 1 < n, Nat.gcd n (a ⟨r + 1, hr⟩ - a ⟨r, by omega⟩).val = Nat.gcd n (b ⟨r + 1, hr⟩ - b ⟨r, by omega⟩).val.
-/

/-- Two orderings share the same consecutive symbol-difference gcd sequence. -/
def cyclic_consecutive_gcd_eq {n : ℕ} (a b : Fin n ≃ ZMod n) : Prop :=
  ∀ (r : ℕ) (hr : r + 1 < n),
    Nat.gcd n (a ⟨r + 1, hr⟩ - a ⟨r, by omega⟩).val =
      Nat.gcd n (b ⟨r + 1, hr⟩ - b ⟨r, by omega⟩).val
