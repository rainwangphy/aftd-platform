import AFTD.Prelude

/-!
# harborth_double_hom

Topic: combinatorics   Node: fbbb88612444

Provenance: helper lemma. step towards harborth_bound_rank_three_mul_two

The additive map ZMod k → ZMod (2k) sending x to 2x (multiplication by 2 through composite ZMod.lift).
-/

noncomputable def harborth_double_hom (k : ℕ) : ZMod k →+ ZMod (2 * k) := ZMod.lift k ⟨(Int.castAddHom (ZMod (2 * k))).comp
      (AddMonoidHom.mk' (fun m : ℤ => 2 * m) (fun a b => by ring)),
    by
      show ((2 * (k : ℤ) : ℤ) : ZMod (2 * k)) = 0
      rw [show ((2 * (k : ℤ) : ℤ) : ZMod (2 * k)) = ((2 * k : ℕ) : ZMod (2 * k)) by
        push_cast; ring]
      exact ZMod.natCast_self (2 * k)⟩
