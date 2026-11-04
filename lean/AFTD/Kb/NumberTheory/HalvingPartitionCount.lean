import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsHalvingPartition

/-!
# halving_partition_count

Topic: elementary_number_theory   Node: 0b4746287c3a

Provenance: formalization of a published result. Source: arXiv:2611.01243 Definition 1

The number of halving partitions of $n$, denoted $a(n)$, is the cardinality (using `Set.ncard`) of the set of lists $p$ of positive integers that are halving partitions of $n$ (satisfying `is_halving_partition n p`), which are sequences $(p_1, \dots, p_k)$ summing to $n$ where $p_1 \in \{\lfloor n/2 \rfloor, \lceil n/2 \rceil\}$ and each successive part $p_i \in \{\lfloor p_{i-1}/2 \rfloor, \lceil p_{i-1}/2 \rceil\}$, with the empty list being the unique halving partition of $0$.
-/

/-- The number of halving partitions of n, denoted a(n) in arXiv:2611.01243. -/
noncomputable def halving_partition_count (n : ℕ) : ℕ := Set.ncard { p : List ℕ | is_halving_partition n p }
