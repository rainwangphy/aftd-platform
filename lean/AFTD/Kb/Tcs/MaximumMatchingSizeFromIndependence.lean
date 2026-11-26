import AFTD.Prelude
import AFTD.Kb.Tcs.MaximumMatchingUnmatchedIndependent
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# maximum_matching_size_from_independence

Topic: graphs   Node: aa4675ec3686

Provenance: helper lemma. Balanced-cut matching symmetry for OP-1957; https://arxiv.org/abs/2611.22690.

A maximum matching inside S covers enough vertices that |S| is at most twice its edge count plus the independence bound.
-/

theorem maximum_matching_size_from_independence
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (M : G.Subgraph) (hM : M.IsMatching)
    (hMS : M.verts ⊆ (S : Set V))
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.verts ⊆ (S : Set V) → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    (a : ℕ) (hind : ∀ U : Finset V,
      (∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v) → U.card ≤ a) :
    S.card ≤ 2*M.edgeSet.ncard+a := by
  set_option maxHeartbeats 4000000 in
    classical
    let D : Finset V := M.verts.toFinset
    let U : Finset V := S \ D
    have hDS : D ⊆ S := by intro v hv; exact hMS (by simpa [D] using hv)
    have hDcard : D.card = 2*M.edgeSet.ncard := by
      dsimp [D]
      rw [← Set.ncard_eq_toFinset_card']
      exact (in1076_matching_twice_card hM).symm
    have hUind : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v := by
      intro u hu v hv hne
      have hu' := Finset.mem_sdiff.mp hu
      have hv' := Finset.mem_sdiff.mp hv
      apply maximum_matching_unmatched_independent G S M hM hMS hmax u hu'.1 ?_ v hv'.1 ?_
      · simpa [D] using hu'.2
      · simpa [D] using hv'.2
    have hU := hind U hUind
    have hcount := Finset.card_sdiff_add_card_eq_card hDS
    dsimp [U] at hU
    omega
