import AFTD.Prelude

/-!
# qary_canonical_spaced_word

Topic: information   Node: ef92fe457700

Provenance: formalization of a published result. Source: knowledgebase, OP-1503

For natural numbers t, q, and n with t + 1 ≤ q, the canonical spaced word of length n is the word sending each index i : Fin n to (i.val % (t + 1) : Fin q).
-/

/-- Canonical periodic word 0, 1, ..., t, 0, 1, ... of length n over Fin q. -/
def qary_canonical_spaced_word (t q n : ℕ) (htq : t + 1 ≤ q) : Fin n → Fin q := fun i : Fin n => ⟨i.val % (t + 1), lt_of_lt_of_le (Nat.mod_lt _ (Nat.succ_pos t)) htq⟩
