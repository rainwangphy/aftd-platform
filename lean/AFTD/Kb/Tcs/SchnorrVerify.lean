import AFTD.Prelude

/-!
# Schnorr.Verify

Topic: cryptography   Node: 658f6922838f

Provenance: formalization of a published result. Source: TCSlib, `Schnorr.Verify`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

The verifier accepts a transcript $(a, c, s)$ with respect to public key
$\mathit{pk} \in G$ when $g^s = a \cdot \mathit{pk}^{c}$, where the
exponents are taken via the canonical lifts to $\mathbb{N}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- Verifier's accept predicate: `g ^ s = a · pk ^ c`. -/
def Schnorr.Verify (pk a : G) (c s : ZMod q) : Prop :=
  g ^ s.val = a * pk ^ c.val
