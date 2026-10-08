import AFTD.Prelude

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

Topic: cryptography   Node: 32250354a813

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Encryption.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A private-key encryption scheme over message space `M`, key space `K`, and ciphertext space `C` ([KatzLindell2020], Definition 2.1).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A private-key encryption scheme over message space `M`, key space `K`, and ciphertext space `C` ([KatzLindell2020], Definition 2.1). -/
structure Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme (Message Key Ciphertext : Type*) where
  /-- Probabilistic key generation. -/
  gen : PMF Key
  /-- (Possibly randomized) encryption. -/
  enc (key : Key) (message : Message) : PMF Ciphertext
  /-- Deterministic decryption. -/
  dec (key : Key) (ciphertext : Ciphertext) : Message
  /-- Decryption inverts encryption for all keys in the support of `gen`. -/
  correct : ∀ key, key ∈ gen.support → ∀ message ciphertext,
    ciphertext ∈ (enc key message).support → dec key ciphertext = message
