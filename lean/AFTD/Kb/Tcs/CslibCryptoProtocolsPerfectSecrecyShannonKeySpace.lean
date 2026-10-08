import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyCiphertextIndistOfPerfectlySecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextIndist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncryptKeyInjective
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePerfectlySecret

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.shannonKeySpace

Topic: cryptography   Node: 50c3a9f69d4e

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.shannonKeySpace`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/PerfectSecrecy.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Perfect secrecy requires `|K| ≥ |M|` (Shannon's theorem).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PMF ENNReal in
universe u in
variable {M K C : Type u} in
/-- Perfect secrecy requires `|K| ≥ |M|` (Shannon's theorem). -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.shannonKeySpace [Finite K]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret) :
    Nat.card K ≥ Nat.card M := by
  classical
  have hci := ciphertextIndist_of_perfectlySecret scheme h
  by_cases hM : IsEmpty M; · simp
  obtain ⟨m₀⟩ := not_isEmpty_iff.mp hM
  obtain ⟨c₀, hc₀⟩ := (scheme.ciphertextDist m₀).support_nonempty
  have key_exists : ∀ m, ∃ k ∈ scheme.gen.support, c₀ ∈ (scheme.enc k m).support := by
    intro m
    exact (PMF.mem_support_bind_iff _ _ _).mp
      (show c₀ ∈ (scheme.ciphertextDist m).support by rw [hci m m₀]; exact hc₀)
  choose f hf_mem hf_enc using key_exists
  exact Nat.card_le_card_of_injective f
    (encrypt_key_injective scheme f c₀ hf_mem hf_enc)
