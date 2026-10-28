import AFTD.Prelude
import AFTD.Kb.Tcs.PartitionA
import AFTD.Kb.Tcs.IsTIntersectingPartitionFamily

/-!
# partition_A_is_one_intersecting

Topic: combinatorics   Node: 044da95f83d0

Provenance: helper lemma. arXiv:2610.01747, Proposition 6.1

For every n, any two partitions in A_n share at least one common part, so A_n is 1-intersecting.
-/

/-- The family A_n is 1-intersecting for any n. -/
theorem partition_A_is_one_intersecting (n : ℕ) :
    is_t_intersecting_partition_family 1 (partition_A n) := by
  intro p hp q hq
  rw [partition_A, Finset.mem_filter] at hp hq
  obtain ⟨-, hp⟩ := hp
  obtain ⟨-, hq⟩ := hq
  have h_inter : ∃ x, x ∈ p.parts ∧ x ∈ q.parts := by
    rcases hp with ⟨h1p, h2p⟩ | ⟨h1p, h3p⟩ | ⟨h1p, h4p⟩ | ⟨h2p, h3p, h4p⟩
    · rcases hq with ⟨h1q, -⟩ | ⟨h1q, -⟩ | ⟨h1q, -⟩ | ⟨h2q, -, -⟩
      · exact ⟨1, h1p, h1q⟩
      · exact ⟨1, h1p, h1q⟩
      · exact ⟨1, h1p, h1q⟩
      · exact ⟨2, h2p, h2q⟩
    · rcases hq with ⟨h1q, -⟩ | ⟨h1q, -⟩ | ⟨h1q, -⟩ | ⟨-, h3q, -⟩
      · exact ⟨1, h1p, h1q⟩
      · exact ⟨1, h1p, h1q⟩
      · exact ⟨1, h1p, h1q⟩
      · exact ⟨3, h3p, h3q⟩
    · rcases hq with ⟨h1q, -⟩ | ⟨h1q, -⟩ | ⟨h1q, -⟩ | ⟨-, -, h4q⟩
      · exact ⟨1, h1p, h1q⟩
      · exact ⟨1, h1p, h1q⟩
      · exact ⟨1, h1p, h1q⟩
      · exact ⟨4, h4p, h4q⟩
    · rcases hq with ⟨-, h2q⟩ | ⟨-, h3q⟩ | ⟨-, h4q⟩ | ⟨h2q, -, -⟩
      · exact ⟨2, h2p, h2q⟩
      · exact ⟨3, h3p, h3q⟩
      · exact ⟨4, h4p, h4q⟩
      · exact ⟨2, h2p, h2q⟩
  obtain ⟨x, hxp, hxq⟩ := h_inter
  have hx : x ∈ p.parts ∩ q.parts := Multiset.mem_inter.mpr ⟨hxp, hxq⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx⟩
