import AFTD.Prelude
import AFTD.Kb.Tcs.SchnorrVerify

/-!
# schnorr_response_unique

Topic: cryptography   Node: a1e8b9d0ca0e

Provenance: formalization of a published result. Source: Schnorr (1991); Katz & Lindell (2020), Section 12.5.1

In the Schnorr identification protocol, accepting responses are unique: let G be a commutative group, q a prime, and g in G an element of order q. For any public key pk in G, commitment a in G, and challenge c in ZMod q, if responses s₁, s₂ in ZMod q both satisfy Schnorr.Verify g pk a c s₁ and Schnorr.Verify g pk a c s₂, then s₁ = s₂.
-/

/-- For a fixed commitment and challenge, the Schnorr verifier accepts at most one response. -/
theorem schnorr_response_unique {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (pk a : G) (c s₁ s₂ : ZMod q)
    (h₁ : Schnorr.Verify g pk a c s₁) (h₂ : Schnorr.Verify g pk a c s₂) :
    s₁ = s₂ := by
  have : NeZero q := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h_pow : g ^ s₁.val = g ^ s₂.val := by
    change g ^ s₁.val = a * pk ^ c.val at h₁
    change g ^ s₂.val = a * pk ^ c.val at h₂
    rw [h₁, h₂]
  rw [pow_eq_pow_iff_modEq, hg] at h_pow
  have h_val : s₁.val = s₂.val := by
    have hs₁ := ZMod.val_lt s₁
    have hs₂ := ZMod.val_lt s₂
    change s₁.val % q = s₂.val % q at h_pow
    rwa [Nat.mod_eq_of_lt hs₁, Nat.mod_eq_of_lt hs₂] at h_pow
  exact ZMod.val_injective q h_val
