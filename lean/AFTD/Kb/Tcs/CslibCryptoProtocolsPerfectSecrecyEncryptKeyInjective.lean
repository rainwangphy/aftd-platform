import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.Support

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.encrypt_key_injective

Topic: cryptography   Node: 64ef855d9361

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.encrypt_key_injective`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/PerfectSecrecy.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If each message maps to a key that encrypts it to a common ciphertext, then the key assignment is injective (by correctness of decryption).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PMF ENNReal in
universe u in
variable {M K C : Type u} in
/-- If each message maps to a key that encrypts it to a common ciphertext, then the key assignment is injective (by correctness of decryption). -/
lemma Cslib.Crypto.Protocols.PerfectSecrecy.encrypt_key_injective (scheme : EncScheme M K C)
    (f : M → K) (c₀ : C)
    (hf_mem : ∀ m, f m ∈ scheme.gen.support)
    (hf_enc : ∀ m, c₀ ∈ (scheme.enc (f m) m).support) :
    Function.Injective f :=
  fun m₁ m₂ heq =>
    (scheme.correct _ (hf_mem m₁) m₁ c₀ (hf_enc m₁)).symm.trans
      (heq ▸ scheme.correct _ (hf_mem m₂) m₂ c₀ (hf_enc m₂))
