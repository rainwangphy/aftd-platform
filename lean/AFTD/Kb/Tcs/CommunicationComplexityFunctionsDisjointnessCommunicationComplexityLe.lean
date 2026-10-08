import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessDisjointness
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessClogTwoTwo
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexityLeClogCardXAlpha

/-!
# CommunicationComplexity.Functions.Disjointness.communicationComplexity_le

Topic: communication   Node: 80b6f39cdade

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Functions.Disjointness.communicationComplexity_le`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncDisjointness.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Upper bound on the communication complexity of disjointness. Fix $n \in \bbn$, and let both players' inputs range over subsets of $[n] = \{0, 1,
\dots, n-1\}$, so that Alice holds $X \subseteq [n]$ and Bob holds $Y \subseteq [n]$.
The deterministic communication complexity of the set-disjointness function, which
returns $\mathtt{true}$ exactly when $X \cap Y = \emptyset$, is at most $n + 1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open scoped symmDiff in
/-- The deterministic communication complexity of disjointness on subsets of `[n]` is at most `n + 1`: Alice sends her set as `n` bits, and Bob sends one bit for the answer [RY20, Ch. 1, §Disjointness: 'Alice sending X gives an (n+1)-bit protocol']. -/
theorem CommunicationComplexity.Functions.Disjointness.communicationComplexity_le (n : ℕ) :
    Deterministic.communicationComplexity (disjointness n) ≤ n + 1 := by
  calc Deterministic.communicationComplexity (disjointness n)
      ≤ Nat.clog 2 (Nat.card (Set (Fin n))) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_X_alpha (disjointness n)
    _ = n + 1 := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin,
          Fintype.card_bool, Nat.one_lt_ofNat, Nat.clog_pow]
        rw [clog_two_two]
        norm_num
