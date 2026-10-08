import AFTD.Prelude

/-!
# CommunicationComplexity.Internal.enat_iInf_le_coe_iff

Topic: communication   Node: 798d406cfa8b

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.enat_iInf_le_coe_iff`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetComplexity.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Infimum of an extended-natural family bounded by a coercion. Let $(f_i)_{i \in \iota}$ be a family of values in the extended natural numbers
$\bbn_\infty = \bbn \cup \{\infty\}$, indexed by an arbitrary type $\iota$, and let $n
\in \bbn$. Then $\inf_{i} f_i \le n$ if and only if there exists an index $i$ with $f_i
\le n$, where $n$ is regarded as an element of $\bbn_\infty$ via the canonical
inclusion.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- An infimum of extended naturals is at most a natural number `n` if and only if some term of the family is at most `n`. (This uses that `n` is finite: an infimum of values all `≥ n + 1` is `≥ n + 1`.) -/
@[simp]
theorem CommunicationComplexity.Internal.enat_iInf_le_coe_iff {ι : Sort*} {f : ι → ENat} {n : ℕ} :
    iInf f ≤ ↑n ↔ ∃ i, f i ≤ ↑n := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply not_lt.mpr h
    have : ∀ i, (↑(n + 1) : ENat) ≤ f i := fun i => by
      match f i, hne i with
      | none, _ => exact le_top
      | some m, hi =>
        exact WithTop.coe_le_coe.mpr
          (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hi))
    exact lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n))
      (le_iInf this)
  · rintro ⟨i, hi⟩
    exact (iInf_le f i).trans hi
