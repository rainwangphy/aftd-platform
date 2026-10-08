import AFTD.Prelude
import AFTD.Kb.Tcs.BernoulliMgfBound

/-!
# hoeffding_lemma

Topic: learning   Node: d0109a6346a1

Provenance: helper lemma. TCSlib, `hoeffding_lemma`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Regret.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Hoeffding's lemma. Let $p \in [0,1]$ and let $h \in \bbr$ be arbitrary. Then
\[
  \log\!\bigl((1-p) + p\,e^{h}\bigr) \;\le\; p\,h + \frac{h^{2}}{8}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- **Hoeffding's lemma**, Bernoulli case: for `p ∈ [0,1]` and any real `h`, `ln((1-p) + p·eʰ) ≤ p·h + h²/8`; that is, the log-moment generating function of a `{0,1}`-valued random variable with mean `p` is at most `p·h + h²/8` [CBL06, Lemma 2.2]; [MRT18, Lemma D.1]. Deviation: only the two-point distribution on `{0,1}` (range length `b - a = 1`) is covered, not a general `[a,b]`-valued variable. Specializes `bernoulli_mgf_bound` from `Hedge.Hoeffding` by substituting `η = -h`. -/
lemma hoeffding_lemma {p h : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.log ((1 - p) + p * Real.exp h) ≤ p * h + h ^ 2 / 8 := by
  have hb := bernoulli_mgf_bound p (-h) hp0 hp1
  simp only [neg_neg] at hb
  linarith [show -p * -h + (-h) ^ 2 / 8 = p * h + h ^ 2 / 8 from by ring]
