import AFTD.Prelude
import AFTD.Kb.Tcs.FifoQueue

/-!
# fifo_rank

Topic: online_algorithms   Node: 1a41b5847d16

Provenance: formalization of a published result. Source: arXiv:2610.18767 Section 3.2

The rank of a page in a FIFO queue of size k, ranging from 1 for the oldest page (next to be evicted) to k for the most recently fetched page, or 0 if absent.
-/

/-- Rank of a page in the FIFO queue from 1 (oldest) to k (newest). -/
def fifo_rank {α : Type*} [DecidableEq α] {k : ℕ} (q : FifoQueue α k) (x : α) : ℕ := if x ∈ q.pages then q.pages.idxOf x + 1 else 0
