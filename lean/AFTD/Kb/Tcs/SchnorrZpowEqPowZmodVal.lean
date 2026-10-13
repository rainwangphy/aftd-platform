import AFTD.Prelude

/-!
# schnorr_zpow_eq_pow_zmod_val

Topic: cryptography   Node: 6f608317990a

Provenance: helper lemma. folklore

Let G be a commutative group, q a prime, and g in G an element of order q. For any integer z, the integer power g^z equals g^(z.val) where z is viewed in ZMod q via its canonical lift to Nat.
-/

/-- In a cyclic subgroup of prime order q, integer powers equal powers of the canonical ZMod q representative. -/
theorem schnorr_zpow_eq_pow_zmod_val {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (z : ℤ) :
    g ^ z = g ^ (z : ZMod q).val := by
  have h_pow : g ^ q = 1 := by rw [← hg, pow_orderOf_eq_one]
  rw [zpow_eq_zpow_emod' z h_pow, ← ZMod.val_intCast z, zpow_natCast]
