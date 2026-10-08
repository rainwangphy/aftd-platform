import AFTD.Prelude

/-!
# Schnorr.commit

Topic: cryptography   Node: deb02476a0d0

Provenance: formalization of a published result. Source: TCSlib, `Schnorr.commit`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

Given randomness $r \in \mathbb{Z}_q$ and a generator $g \in G$, the commitment
is $a := g^{r}$, where the exponent is taken via the canonical lift
$r.\mathrm{val} \in \mathbb{N}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- Prover's first message: commitment `a := g ^ r` for randomness `r`. -/
def Schnorr.commit (r : ZMod q) : G := g ^ r.val
