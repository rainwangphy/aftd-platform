import AFTD.Prelude

/-!
# Schnorr.respond

Topic: cryptography   Node: 8b4b23681a7c

Provenance: formalization of a published result. Source: TCSlib, `Schnorr.respond`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

Given witness $w$, randomness $r$, and challenge $c$ in $\mathbb{Z}_q$, the
response is $s := r + c \cdot w \in \mathbb{Z}_q$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- Prover's second message: response `s := r + c·w` for witness `w`, randomness `r`, challenge `c`. -/
def Schnorr.respond (w r c : ZMod q) : ZMod q := r + c * w
