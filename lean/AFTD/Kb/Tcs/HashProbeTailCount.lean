import AFTD.Prelude
import AFTD.Kb.Tcs.HashOccupiedSlots

/-!
# hash_probe_tail_count

Topic: data_structures   Node: 2c8b11b7ea0d

Provenance: formalization of a published result. Source: arXiv:2610.31363, Section 2

The number of pairs of an insertion sequence of length t and an additional query slot whose insertion cost under offset sequence r strictly exceeds k, meaning the first k probed slots are all occupied.
-/

/-- Number of insertion-query pairs requiring strictly more than k probes. -/
def hash_probe_tail_count (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (t k : ℕ) : ℕ :=
  (Finset.univ.filter (fun (p : (Fin t → ZMod n) × ZMod n) =>
    ∀ j : Fin n, j.val < k → p.2 + r j ∈ hash_occupied_slots n r (List.ofFn p.1))).card
