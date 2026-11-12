import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingBoundary
import AFTD.Kb.Tcs.ZeroForcingSeq
import AFTD.Kb.Tcs.ZeroForcingCl
import AFTD.Kb.Tcs.ZeroForcingBoundaryMono
import AFTD.Kb.Tcs.ZeroForcingBoundaryClLe

/-!
# zero_forcing_boundary_monotonicity

Topic: graphs   Node: bb6824ae8fec

Provenance: formalization of a published result. Source: arXiv:2611.13244, Proposition 2.9 -- Stabilization of the zero forcing number of generalized Petersen graphs

Let G be a simple graph, and let S be a finite subset of vertices. In the zero forcing sequence B_0 = S ⊆ B_1 ⊆ ..., the extended cardinality of ∂B_{i+1} is at most that of ∂B_i for every i ≥ 0. In particular, the extended cardinality of ∂B_i is at most that of S for every i ≥ 0, and the extended cardinality of ∂cl(S) is at most that of S.
-/

/-- Boundary monotonicity along the zero forcing process: |∂B_{i+1}| ≤ |∂B_i| for all i, |∂B_i| ≤ |S| for all i, and |∂cl(S)| ≤ |S|. -/
theorem zero_forcing_boundary_monotonicity {V : Type*} (G : SimpleGraph V) {S : Set V} (hS : S.Finite) : (∀ i : ℕ, (zero_forcing_boundary G (zero_forcing_seq G S (i + 1))).encard ≤ (zero_forcing_boundary G (zero_forcing_seq G S i)).encard) ∧ (∀ i : ℕ, (zero_forcing_boundary G (zero_forcing_seq G S i)).encard ≤ S.encard) ∧ (zero_forcing_boundary G (zero_forcing_cl G S)).encard ≤ S.encard := ⟨zero_forcing_boundary_mono G hS, zero_forcing_boundary_cl_le_seq_le G hS, zero_forcing_boundary_cl_le G hS⟩
