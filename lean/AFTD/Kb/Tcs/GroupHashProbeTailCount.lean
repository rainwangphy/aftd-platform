import AFTD.Prelude
import AFTD.Kb.Tcs.GroupHashOccupiedSlots

/-!
# group_hash_probe_tail_count

Topic: data_structures   Node: 0166fc358cc8

Provenance: formalization of a published result. Source: arXiv:2610.31363: A Sharp Analysis of Fixed Offset Hash Tables

Given a finite group G with decidable equality, a table size n : ℕ, an offset sequence r : Fin n → G, and natural numbers t and c, group_hash_probe_tail_count G n r t c is the cardinality of the finset of pairs (A, q) in (Fin t → G) × G such that for all j : Fin n with (j : ℕ) < c, q * r j belongs to group_hash_occupied_slots n r (List.ofFn A).
-/

/-- The number of insertion histories and query keys requiring strictly more than c probes. -/
def group_hash_probe_tail_count (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (n : ℕ) (r : Fin n → G) (t c : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin t → G) × G)).filter fun (A, q) =>
    ∀ j : Fin n, (j : ℕ) < c → q * r j ∈ group_hash_occupied_slots n r (List.ofFn A)).card
