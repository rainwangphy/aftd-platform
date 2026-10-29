import AFTD.Prelude

/-!
# harborth_parity

Topic: combinatorics   Node: 3f5211ec49ce

Provenance: helper lemma. step towards harborth_bound_rank_three_mul_two

The parity map (ZMod (2k))^3 → (ZMod 2)^3, componentwise reduction mod 2.
-/

def harborth_parity (k : ℕ) : (Fin 3 → ZMod (2 * k)) → (Fin 3 → ZMod 2) := fun v i => ZMod.cast (v i)
