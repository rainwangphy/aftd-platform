import AFTD.Prelude

/-!
# Cslib.Crypto.Protocols.SecretSharing.viewDistOf

Topic: cryptography   Node: 434b0e75faec

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.viewDistOf`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Scheme.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The view distribution induced by raw sharing data.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The view distribution induced by raw sharing data. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.viewDistOf {Secret Randomness Party Share : Type*}
    (gen : PMF Randomness) (share : Randomness → Secret → Party → Share)
    (s : Finset Party) (secret : Secret) : PMF (s → Share) :=
  PMF.map (fun r : Randomness => (fun i : s => share r secret i : s → Share)) gen
