import AFTD.Prelude
import AFTD.Kb.Tcs.SchnorrVerify

/-!
# schnorr_soundness_affine_related_keys

Topic: cryptography   Node: b2083cb843e0

Provenance: original. Related work: Goldreich, Foundations of Cryptography, vol. 1, Sec. 4.4

Let G be a commutative group, q a prime, and g in G an element of order q. Let w₁ in ZMod q be a secret witness and pk₁ = g^(w₁.val). Let α, β in ZMod q define a related witness w₂ = α * w₁ + β with public key pk₂ = g^(w₂.val). Suppose an identical commitment a in G is used in two transcripts (a, c₁, s₁) and (a, c₂, s₂) that satisfy Schnorr.Verify for pk₁ and pk₂ respectively. If c₁ ≠ α * c₂, then (s₁ - s₂ + β * c₂) / (c₁ - α * c₂) = w₁ in ZMod q.
-/

/-- Special soundness of the Schnorr protocol with affine-related keys: nonce reuse across related keys extracts the primary witness. -/
theorem schnorr_soundness_affine_related_keys
    {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (w₁ α β : ZMod q) (a : G)
    (c₁ c₂ s₁ s₂ : ZMod q) (hne : c₁ ≠ α * c₂)
    (h₁ : Schnorr.Verify g (g ^ w₁.val) a c₁ s₁)
    (h₂ : Schnorr.Verify g (g ^ (α * w₁ + β).val) a c₂ s₂) :
    (s₁ - s₂ + β * c₂) / (c₁ - α * c₂) = w₁ := by
  simp only [Schnorr.Verify] at h₁ h₂
  have key1 : g ^ s₁.val * (g ^ (α * w₁ + β).val) ^ c₂.val
      = g ^ s₂.val * (g ^ w₁.val) ^ c₁.val := by
    rw [h₁, h₂, mul_right_comm]
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      pow_eq_pow_iff_modEq, hg] at key1
  have hZ : s₁ + (α * w₁ + β) * c₂ = s₂ + w₁ * c₁ := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ q).mpr key1
  have hsub : s₁ - s₂ + β * c₂ = w₁ * (c₁ - α * c₂) := by
    linear_combination hZ
  have hc_ne : c₁ - α * c₂ ≠ 0 := sub_ne_zero.mpr hne
  rw [div_eq_iff hc_ne]
  exact hsub
