import AFTD.Prelude
import AFTD.Kb.Tcs.HarborthHalf

/-!
# harborth_pair_key

Topic: combinatorics   Node: 489f800d95b4

Provenance: helper lemma. step towards harborth_bound_rank_three_mul_two

The key of a pair of vectors: componentwise half of the componentwise sum.
-/

noncomputable def harborth_pair_key (k : ℕ) (p : (Fin 3 → ZMod (2 * k)) × (Fin 3 → ZMod (2 * k))) : Fin 3 → ZMod k := fun i => harborth_half k (p.1 i + p.2 i)
