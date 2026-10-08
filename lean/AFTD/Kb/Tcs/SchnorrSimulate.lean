import AFTD.Prelude
import AFTD.Kb.Tcs.SchnorrTranscript

/-!
# Schnorr.simulate

Topic: cryptography   Node: 3d3eefd7a1e8

Provenance: formalization of a published result. Source: TCSlib, `Schnorr.simulate`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

The zero-knowledge simulator, given public key $\mathit{pk}$, challenge $c$,
and a fresh response $s$, outputs the transcript
$(g^s \cdot (\mathit{pk}^c)^{-1},\; c,\; s)$.
The commitment is chosen so that the transcript is accepting without using the
witness.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- Simulator transcript for challenge `c` and fresh response `s`, setting `a := g^s · (pk^c)⁻¹`. Does not use the witness. -/
def Schnorr.simulate (pk : G) (c s : ZMod q) : Transcript G q :=
  (g ^ s.val * (pk ^ c.val)⁻¹, c, s)
