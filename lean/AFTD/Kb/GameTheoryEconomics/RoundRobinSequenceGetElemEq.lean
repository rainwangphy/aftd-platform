import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence

/-!
# round_robin_sequence_getElem?_eq

Topic: fair_division   Node: a6760a9cde46

Provenance: helper lemma. step towards round_robin_two_mul_add_one_deviation_certificate

The t-th turn (for t < m) of the Round-Robin sequence of n agents is agent t mod n.
-/

/-- The t-th turn of the Round-Robin sequence of n agents is agent t % n. -/
theorem round_robin_sequence_getElem?_eq (n m : ℕ) [NeZero n] (t : ℕ) (h : t < m) :
    (round_robin_sequence n m)[t]? = some (⟨t % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) := by
  simp [round_robin_sequence, List.getElem?_ofFn, h]
