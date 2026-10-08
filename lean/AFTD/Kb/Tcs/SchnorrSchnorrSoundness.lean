import AFTD.Prelude
import AFTD.Kb.Tcs.SchnorrVerify
import AFTD.Kb.Tcs.SchnorrExtract

/-!
# Schnorr.schnorr_soundness

Topic: cryptography   Node: 75efb39542c5

Provenance: formalization of a published result. Source: Special soundness of the Schnorr protocol, as formalized in TCSlib (`Schnorr.schnorr_soundness`). Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

Special soundness of the Schnorr protocol. Special soundness. Let $q$ be prime, let $g$ be an element of order $q$ in a commutative
group $G$, and take the public key $\mathit{pk} = g^{w}$ for some witness $w \in
\bbz_q$. Suppose $a \in G$, and suppose $c_1, c_2 \in \bbz_q$ are distinct challenges
with responses $s_1, s_2 \in \bbz_q$ such that both transcripts $(a, c_1, s_1)$ and $(a,
c_2, s_2)$ are accepted by the verifier for $\mathit{pk}$. Then the extractor recovers
the witness:
\[
  \frac{s_1 - s_2}{c_1 - c_2} \;=\; w \quad\text{in } \bbz_q.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- **Special soundness**: given a generator `g` of order `q` and two accepting transcripts `(a, c₁, s₁)` and `(a, c₂, s₂)` for public key `pk = g^w` that share the commitment `a` but use distinct challenges `c₁ ≠ c₂`, the extractor recovers the witness: `(s₁ - s₂) / (c₁ - c₂) = w` in `ZMod q`. -/
theorem Schnorr.schnorr_soundness
    (hg : orderOf g = q)
    (w : ZMod q) (a : G) (c₁ c₂ s₁ s₂ : ZMod q) (hne : c₁ ≠ c₂)
    (h₁ : Verify g (g ^ w.val) a c₁ s₁)
    (h₂ : Verify g (g ^ w.val) a c₂ s₂) :
    extract c₁ c₂ s₁ s₂ = w := by
  simp only [Verify] at h₁ h₂
  have key1 : g ^ s₁.val * (g ^ w.val) ^ c₂.val
      = g ^ s₂.val * (g ^ w.val) ^ c₁.val := by
    rw [h₁, h₂, mul_right_comm]
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      pow_eq_pow_iff_modEq, hg] at key1
  have hZ : s₁ + w * c₂ = s₂ + w * c₁ := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ q).mpr key1
  have hsub : s₁ - s₂ = w * (c₁ - c₂) := by linear_combination hZ
  have hc_ne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  rw [extract, div_eq_iff hc_ne]
  exact hsub
