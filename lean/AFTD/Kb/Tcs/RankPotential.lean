import AFTD.Prelude
import AFTD.Kb.Tcs.FifoQueue
import AFTD.Kb.Tcs.FifoRank

/-!
# rank_potential

Topic: online_algorithms   Node: 760b3a481acf

Provenance: formalization of a published result. Source: arXiv:2610.18767 Section 3.2, Eq. (1)

The rank potential function Φ for FIFO paging, defined as the sum of ranks of all pages currently in the online FIFO cache but absent from the offline cache.
-/

/-- Rank potential Φ summing ranks of online cached pages outside offline cache. -/
def rank_potential {α : Type*} [DecidableEq α] {k : ℕ} (q : FifoQueue α k) (cOpt : Finset α) : ℕ := ∑ x ∈ q.pages.toFinset \ cOpt, fifo_rank q x
