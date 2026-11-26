import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.Op2037SubgraphFintype

/-!
# finite_subset_has_maximum_matching

Topic: graphs   Node: d1fe47120145

Provenance: helper lemma. Balanced-cut matching symmetry for OP-1957; https://arxiv.org/abs/2611.22690.

Every vertex subset of a finite graph contains a maximum matching.
-/

theorem finite_subset_has_maximum_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts ⊆ (S : Set V) ∧
      ∀ N : G.Subgraph, N.IsMatching → N.verts ⊆ (S : Set V) → N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  set_option maxHeartbeats 4000000 in
    classical
    let P : ℕ → Prop := fun n => ∃ M : G.Subgraph, M.IsMatching ∧ M.verts ⊆ (S : Set V) ∧ M.edgeSet.ncard = n
    have hzero : P 0 := by
      refine ⟨⊥,?_,?_,?_⟩
      · intro v hv
        simp at hv
      · simp
      · simp
    have hP : P (Nat.findGreatest P S.card) := Nat.findGreatest_spec (by omega : 0 ≤ S.card) hzero
    obtain ⟨M,hM,hMS,hMcard⟩ := hP
    refine ⟨M,hM,hMS,?_⟩
    intro N hN hNS
    have hNbound : N.edgeSet.ncard ≤ S.card := by
      have he := in1076_matching_twice_card hN
      have hv := Set.ncard_le_ncard hNS (Set.toFinite _)
      rw [Set.ncard_coe_finset] at hv
      omega
    by_contra hn
    have hgt : Nat.findGreatest P S.card < N.edgeSet.ncard := by omega
    have hno := Nat.findGreatest_is_greatest hgt hNbound
    exact hno ⟨N,hN,hNS,rfl⟩
