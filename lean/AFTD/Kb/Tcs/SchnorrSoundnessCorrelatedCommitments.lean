import AFTD.Prelude
import AFTD.Kb.Tcs.SchnorrVerify

/-!
# schnorr_soundness_correlated_commitments

Topic: cryptography   Node: 5778e9b6c947

Provenance: formalization of a published result. Source: Ryan (2009), 'Hardware Faults and Schnorr Signatures'; Bellare & Neven (2006)

Special soundness of the Schnorr protocol with affine-correlated commitments: let G be a commutative group, q a prime, and g in G an element of order q. Let w in ZMod q be a witness and pk = g^(w.val) the public key. If two transcripts (a₁, c₁, s₁) and (a₂, c₂, s₂) with distinct challenges c₁ ≠ c₂ both satisfy Schnorr.Verify g (g^(w.val)) a₁ c₁ s₁ and Schnorr.Verify g (g^(w.val)) a₂ c₂ s₂, and the commitments satisfy a₂ = a₁ * g^(Δ.val) for an offset Δ in ZMod q, then (s₁ - s₂ + Δ) / (c₁ - c₂) = w in ZMod q.
-/

/-- Special soundness of Schnorr identification under affine-correlated commitments. -/
theorem schnorr_soundness_correlated_commitments
    {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (w : ZMod q) (a₁ a₂ : G) (Δ : ZMod q)
    (ha : a₂ = a₁ * g ^ Δ.val) (c₁ c₂ s₁ s₂ : ZMod q) (hne : c₁ ≠ c₂)
    (h₁ : Schnorr.Verify g (g ^ w.val) a₁ c₁ s₁)
    (h₂ : Schnorr.Verify g (g ^ w.val) a₂ c₂ s₂) :
    (s₁ - s₂ + Δ) / (c₁ - c₂) = w := by
  simp only [Schnorr.Verify] at h₁ h₂
  have key1 : g ^ s₁.val * g ^ Δ.val * (g ^ w.val) ^ c₂.val
      = g ^ s₂.val * (g ^ w.val) ^ c₁.val := by
    rw [h₁, h₂, ha]
    group
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add,
      pow_eq_pow_iff_modEq, hg] at key1
  have hZ : s₁ + Δ + w * c₂ = s₂ + w * c₁ := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ q).mpr key1
  have hsub : s₁ - s₂ + Δ = w * (c₁ - c₂) := by linear_combination hZ
  have hc_ne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  rw [div_eq_iff hc_ne]
  exact hsub
