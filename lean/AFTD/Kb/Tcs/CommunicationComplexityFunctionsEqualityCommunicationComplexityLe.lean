import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsEqualityEquality
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsEqualityClogTwoTwo
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexityLeClogCardXAlpha

/-!
# CommunicationComplexity.Functions.Equality.communicationComplexity_le

Topic: communication   Node: 99b4c829bc70

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Functions.Equality.communicationComplexity_le`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncEquality.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deterministic complexity upper bound for equality. For every natural number $n$, the deterministic communication complexity of the $n$-bit
equality function satisfies
\[
  D(\mathrm{equality}_n) \;\le\; n+1,
\]
where $\mathrm{equality}_n : \mathrm{BoolInput}\,n \times \mathrm{BoolInput}\,n \to
\mathrm{Bool}$ is the function that returns $\mathtt{true}$ exactly when Alice's input
equals Bob's, and the bound is an inequality in $\bbn_\infty$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- The deterministic communication complexity of equality on `n`-bit strings is at most `n + 1`: Alice sends her `n`-bit input, Bob computes equality and sends one bit [RY20, Ch. 1, §Equality: 'Alice sending her input yields an (n+1)-bit protocol']. -/
theorem CommunicationComplexity.Functions.Equality.communicationComplexity_le (n : ℕ) :
    Deterministic.communicationComplexity (equality n) ≤ n + 1 := by
  calc Deterministic.communicationComplexity (equality n)
      ≤ Nat.clog 2 (Nat.card (Fin n → Bool)) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_X_alpha (equality n)
    _ = n + 1 := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_bool,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.one_lt_ofNat,
          Nat.clog_pow, clog_two_two]
        norm_cast
