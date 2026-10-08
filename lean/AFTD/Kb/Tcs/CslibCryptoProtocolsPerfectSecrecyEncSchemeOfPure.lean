import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ofPure

Topic: cryptography   Node: 7c4af28e9399

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ofPure`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Encryption.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Build an encryption scheme from deterministic pure encryption/decryption where decryption is a left inverse of encryption for every key.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Build an encryption scheme from deterministic pure encryption/decryption where decryption is a left inverse of encryption for every key. -/
noncomputable def Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ofPure.{u} {Message Key Ciphertext : Type u} (gen : PMF Key)
    (enc : Key → Message → Ciphertext) (dec : Key → Ciphertext → Message)
    (h : ∀ key, Function.LeftInverse (dec key) (enc key)) :
    EncScheme Message Key Ciphertext where
  gen := gen
  enc key message := PMF.pure (enc key message)
  dec := dec
  correct key _ message _ hc := by
    rw [PMF.mem_support_pure_iff] at hc; subst hc; exact h key message
