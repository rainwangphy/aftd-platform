import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFoolingSetNcardLePowOfCommunicationComplexityLe
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsFoolingSet

/-!
# CommunicationComplexity.Deterministic.clog_ncard_le_communicationComplexity

Topic: communication   Node: 524f3038c544

Provenance: formalization of a published result. Source: Fooling-set lower bound for deterministic communication complexity, as formalized in TCSlib (`CommunicationComplexity.Deterministic.clog_ncard_le_communicationComplexity`). Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fooling-set lower bound for deterministic communication complexity. Let $g : X \times Y \to \alpha$ be a two-argument function and let $S \subseteq X \times
Y$ be a fooling set for $g$, meaning that every rectangle that is monochromatic for $g$
meets $S$ in at most one point. Then the deterministic communication complexity of $g$
satisfies
\[
  \lceil \log_2 \abs{S} \rceil \;\le\; D(g),
\]
where $\abs{S}$ is the number of elements of $S$ and both sides are compared in
$\bbn_\infty$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Fooling-set lower bound: the deterministic communication complexity of `g` is at least `⌈log₂ |S|⌉` for every fooling set `S` of `g` [Rou16, Cor 4.7] (also [RY20, Ch. 1, §Using Fooling Sets]). Deviation: the ceiling logarithm is `Nat.clog 2`, and the inequality is in `ℕ∞`, so it holds trivially when the complexity is infinite. -/
theorem CommunicationComplexity.Deterministic.clog_ncard_le_communicationComplexity
    (g : X → Y → α) (S : Set (X × Y))
    (hS : Rectangle.IsFoolingSet S g) :
    (Nat.clog 2 (Set.ncard S) : ENat) ≤ communicationComplexity g := by
  match h : communicationComplexity g with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    exact_mod_cast (Nat.clog_le_iff_le_pow (by norm_num)).mpr
      (foolingSet_ncard_le_pow_of_communicationComplexity_le g S n hS (le_of_eq h))
