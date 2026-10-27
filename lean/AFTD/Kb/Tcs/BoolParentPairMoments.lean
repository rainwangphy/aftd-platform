import AFTD.Prelude

/-!
# bool_parent_pair_moments

Topic: combinatorics   Node: b5c5bbe1420e

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

A Boolean parent implication remains valid after multiplication by any bit or its complement, giving two pair-moment inequalities.
-/

open Finset

theorem bool_parent_pair_moments :
    ∀ a b c : Bool, (a = true → b = true) →
      (a && c).toNat ≤ (b && c).toNat ∧
      a.toNat + (b && c).toNat ≤ b.toNat + (a && c).toNat := by
  decide
