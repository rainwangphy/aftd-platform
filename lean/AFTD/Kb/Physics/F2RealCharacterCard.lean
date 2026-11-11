import AFTD.Prelude
import AFTD.Kb.Physics.F2RealCharacterDualEquiv

/-!
# f2_real_character_card

Topic: quantum_mechanics   Node: 59559c81eed0

Provenance: helper lemma. Binary character infrastructure for the OP-827 supported-kernel entropy reduction.

A finite binary vector space has exactly two to the dimension real-valued additive characters.
-/

theorem f2_real_character_card {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Fintype M] :
    Fintype.card (AddChar M ℝ) = 2 ^ Module.finrank (ZMod 2) M := by
  classical
  letI : Finite (M →ₗ[ZMod 2] ZMod 2) := Finite.of_injective (fun f : M →ₗ[ZMod 2] ZMod 2 => (f : M → ZMod 2)) DFunLike.coe_injective
  letI : Fintype (M →ₗ[ZMod 2] ZMod 2) := Fintype.ofFinite _
  calc
    Fintype.card (AddChar M ℝ) = Fintype.card (M →ₗ[ZMod 2] ZMod 2) :=
      Fintype.card_congr f2_real_character_dual_equiv
    _ = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (M →ₗ[ZMod 2] ZMod 2) :=
      Module.card_eq_pow_finrank
    _ = 2 ^ Module.finrank (ZMod 2) M := by simp [Subspace.dual_finrank_eq]
