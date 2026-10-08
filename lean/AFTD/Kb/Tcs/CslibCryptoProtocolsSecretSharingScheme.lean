import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingViewDistOf

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme

Topic: cryptography   Node: 87591da113bc

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Scheme.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A secret-sharing scheme over secret space `Secret`, randomness space `Randomness`, party set `Party`, and share space `Share`. Correctness is deterministic: every authorized coalition reconstructs the secret from the shares generated using any randomness seed. Privacy is distributional: unauthorized coalitions have the same view distribution for all secrets.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A secret-sharing scheme over secret space `Secret`, randomness space `Randomness`, party set `Party`, and share space `Share`. Correctness is deterministic: every authorized coalition reconstructs the secret from the shares generated using any randomness seed. Privacy is distributional: unauthorized coalitions have the same view distribution for all secrets. -/
structure Cslib.Crypto.Protocols.SecretSharing.Scheme (Secret Randomness Party Share : Type*) where
  /-- The distribution used to sample the protocol's randomness. -/
  gen : PMF Randomness
  /-- Sharing algorithm: one randomness seed determines one share per party. -/
  share : Randomness → Secret → Party → Share
  /-- Reconstruction from a coalition's observed shares. -/
  reconstruct (s : Finset Party) : (s → Share) → Secret
  /-- Authorized coalitions. -/
  authorized : Finset Party → Prop
  /-- Authorization is monotone in the coalition. -/
  authorized_mono :
    ∀ {s t : Finset Party}, s ⊆ t → authorized s → authorized t
  /-- Authorized coalitions reconstruct the secret from the restricted view. -/
  correct :
    ∀ (r : Randomness) (secret : Secret) (s : Finset Party),
      authorized s → reconstruct s (fun i => share r secret i) = secret
  /-- Unauthorized coalitions receive secret-independent view distributions. -/
  view_indist :
    ∀ (s : Finset Party), ¬ authorized s → ∀ secret₀ secret₁ : Secret,
      viewDistOf gen share s secret₀ = viewDistOf gen share s secret₁
