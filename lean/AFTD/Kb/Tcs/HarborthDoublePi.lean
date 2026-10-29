import AFTD.Prelude
import AFTD.Kb.Tcs.HarborthDoubleHom

/-!
# harborth_double_pi

Topic: combinatorics   Node: c71e048e2e2c

Provenance: helper lemma. step towards harborth_bound_rank_three_mul_two

The componentwise extension of the doubling map, from (ZMod k)^3 to (ZMod 2k)^3.
-/

noncomputable def harborth_double_pi (k : ℕ) : (Fin 3 → ZMod k) →+ (Fin 3 → ZMod (2 * k)) :=
  { toFun := fun v i => harborth_double_hom k (v i)
    map_zero' := by ext i; exact map_zero _
    map_add' := fun a b => by ext i; exact map_add _ _ _ }
