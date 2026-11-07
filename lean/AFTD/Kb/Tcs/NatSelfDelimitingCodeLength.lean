import AFTD.Prelude
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# nat_self_delimiting_code_length

Topic: computability   Node: 2bc7ea781a3d

Provenance: helper lemma. Sanity check of nat_self_delimiting_code (OP-851 encoding): the code length is linear in the bit length.

The self-delimiting code of m has length twice the number of binary digits of m plus one.
-/

theorem nat_self_delimiting_code_length (m : ℕ) :
    (nat_self_delimiting_code m).length = 2 * (Nat.bits m).length + 1 := by
  simp only [nat_self_delimiting_code, List.length_append, List.length_flatMap, List.length_cons,
    List.length_nil]
  induction Nat.bits m with
  | nil => simp
  | cons b l ih => simp; omega
