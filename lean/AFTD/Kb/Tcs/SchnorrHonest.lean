import AFTD.Prelude
import AFTD.Kb.Tcs.SchnorrTranscript
import AFTD.Kb.Tcs.SchnorrCommit
import AFTD.Kb.Tcs.SchnorrRespond

/-!
# Schnorr.honest

Topic: cryptography   Node: c34c939403f5

Provenance: formalization of a published result. Source: TCSlib, `Schnorr.honest`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

The honest prover's full transcript for witness $w$, randomness $r$, and
challenge $c$ is the triple $(\mathrm{commit}(g, r),\; c,\; \mathrm{respond}(w, r, c))$,
i.e.\ $(g^r,\, c,\, r + c \cdot w)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- Full honest transcript: `(commit g r, c, respond w r c)`. -/
def Schnorr.honest (w r c : ZMod q) : Transcript G q :=
  (commit g r, c, respond w r c)
