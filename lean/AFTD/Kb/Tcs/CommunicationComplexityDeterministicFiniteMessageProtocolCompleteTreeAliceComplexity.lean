import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolCompleteTreeAlice

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_complexity

Topic: communication   Node: 2bb93026b15f

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Complexity of the complete Alice-query tree. Fix a natural number $d$, together with binary query functions
$\mathrm{query}_0,\dots,\mathrm{query}_{d-1} : X \to \mathrm{Bool}$ and a family of
deterministic protocols $Q(\mathrm{bits})$ indexed by the bit patterns $\mathrm{bits} :
\mathrm{Fin}\,d \to \mathrm{Bool}$. Form the protocol that has Alice read the bits
$\mathrm{query}_0(x),\dots,\mathrm{query}_{d-1}(x)$ in sequence and then run $Q$ on the
collected pattern. Its communication complexity is
\[
d + \max_{\mathrm{bits} : \mathrm{Fin}\,d \to \mathrm{Bool}} \;
\mathrm{complexity}\bigl(Q(\mathrm{bits})\bigr),
\]
the maximum being taken over all $2^d$ length-$d$ bit patterns.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The complexity of the complete tree of depth `d` is `d` plus the maximum complexity of the continuations `Q bits` over all bit vectors `bits : Fin d → Bool`. **Proof sketch.** Induction on `d`. For `d = 0` the tree is just `Q Fin.elim0`, and the supremum over the one-element type `Fin 0 → Bool` is that single value. For `d + 1` the root is an Alice node, so the complexity is `1 + max` of the two subtrees, each of which is a complete tree of depth `d` with continuation `bits ↦ Q (Fin.cons b bits)`; applying the induction hypothesis twice reduces the claim to the identity "the supremum over all vectors in `Fin (d + 1) → Bool` is the maximum of the suprema over the vectors starting with `false` and over those starting with `true`", which is proved by splitting `univ` as the union of the images of `Fin.cons false` and `Fin.cons true`. -/
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_complexity (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → Deterministic.Protocol X Y α) :
    (completeTreeAlice d query Q).complexity =
      d + Finset.univ.sup (fun bits => (Q bits).complexity) := by
  induction d with
  | zero =>
    -- Step 1: base case, the supremum over the singleton type `Fin 0 → Bool`
    simp only [completeTreeAlice, Nat.zero_add]
    have : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      simpa using (univ_eq_singleton_of_card_one Fin.elim0 (by simp))
    rw [this, Finset.sup_singleton]
  | succ d ih =>
    -- Unfold to 1 + max (rec false).complexity (rec true).complexity
    simp only [completeTreeAlice, Deterministic.Protocol.complexity]
    rw [ih, ih, Nat.succ_add, Nat.add_max_add_left]
    -- Step 2: split the supremum over `Fin (d + 1) → Bool` by the first bit
    have hsplit : Finset.univ.sup (fun bits : Fin (d + 1) → Bool => (Q bits).complexity) =
        max (Finset.univ.sup (fun bits : Fin d → Bool => (Q (Fin.cons false bits)).complexity))
            (Finset.univ.sup (fun bits : Fin d → Bool => (Q (Fin.cons true bits)).complexity)) := by
      have hdec : (Finset.univ : Finset (Fin (d + 1) → Bool)) =
          (Finset.univ.image (Fin.cons false)) ∪ (Finset.univ.image (Fin.cons true)) := by
        ext bits
        simp only [Finset.mem_univ, Finset.mem_union,
          Finset.mem_image, true_and, true_iff]
        by_cases h : bits 0 = true
        · right; exact ⟨Fin.tail bits, by
            ext i; simp only [Fin.cons]
            refine Fin.cases ?_ ?_ i <;> simp [Fin.tail, h]⟩
        · left; exact ⟨Fin.tail bits, by
            ext i; refine Fin.cases ?_ ?_ i <;>
              simp [Fin.cons, Fin.tail, Bool.eq_false_iff.mpr h]⟩
      rw [hdec, Finset.sup_union, Finset.sup_image, Finset.sup_image]; rfl
    linarith [hsplit]
