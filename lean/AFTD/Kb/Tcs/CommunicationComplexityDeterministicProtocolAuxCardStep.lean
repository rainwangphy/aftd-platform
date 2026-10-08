import AFTD.Prelude

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_card_step

Topic: communication   Node: 53509b8bf2f2

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_card_step`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Union bound for two power-of-two cardinalities. Let $S_0, S_1$ be sets in a type $\beta$ and let $c_0, c_1 \in \mathbb{N}$. If
$\abs{S_0} \le 2^{c_0}$ and $\abs{S_1} \le 2^{c_1}$, then
\[
  \abs{S_0 \cup S_1} \;\le\; 2^{\,1 + \max(c_0, c_1)},
\]
where $\abs{\cdot}$ denotes the number of elements of a set.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Shared counting step of `aux_card`: if `S₀` has at most `2 ^ c₀` elements and `S₁` at most `2 ^ c₁`, then `S₀ ∪ S₁` has at most `2 ^ (1 + max c₀ c₁)` elements. The proof is the union bound, `2 ^ c ≤ 2 ^ max c₀ c₁`, and `2 ^ m + 2 ^ m = 2 ^ (1 + m)`. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_card_step {β : Type*} {S₀ S₁ : Set β} {c₀ c₁ : ℕ}
    (h₀ : S₀.ncard ≤ 2 ^ c₀) (h₁ : S₁.ncard ≤ 2 ^ c₁) :
    (S₀ ∪ S₁).ncard ≤ 2 ^ (1 + max c₀ c₁) :=
  calc (S₀ ∪ S₁).ncard
      ≤ S₀.ncard + S₁.ncard := Set.ncard_union_le _ _
    _ ≤ 2 ^ c₀ + 2 ^ c₁ := Nat.add_le_add h₀ h₁
    _ ≤ 2 ^ max c₀ c₁ + 2 ^ max c₀ c₁ :=
        Nat.add_le_add
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    _ = 2 ^ (1 + max c₀ c₁) := by ring
