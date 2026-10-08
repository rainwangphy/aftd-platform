import AFTD.Prelude

/-!
# Schnorr.Transcript

Topic: cryptography   Node: 618821705280

Provenance: formalization of a published result. Source: TCSlib, `Schnorr.Transcript`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

A Schnorr transcript is a triple $(a, c, s) \in G \times \mathbb{Z}_q \times
\mathbb{Z}_q$, where $a$ is the prover's commitment (an element of the group
$G$), $c \in \mathbb{Z}_q$ is the verifier's challenge, and $s \in \mathbb{Z}_q$
is the prover's response.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- A Schnorr transcript `(a, c, s)`: commitment in `G`, challenge and response in `ZMod q`. -/
abbrev Schnorr.Transcript (G : Type*) (q : ℕ) := G × ZMod q × ZMod q
