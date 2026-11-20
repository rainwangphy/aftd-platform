import AFTD.Prelude
import AFTD.Kb.Tcs.PerfectMatchingForcedEdgeInEveryMatching
import AFTD.Kb.Tcs.PerfectMatchingFalseTwinsSwitchPartner

/-!
# forced_residual_matching_edge_excludes_false_twin

Topic: graphs   Node: a4fcda5e99ce

Provenance: helper lemma. OP-1957 factor-critical forced-bridge shore construction.

A forced matching edge at one false twin excludes the other from the residual.
-/

theorem forced_residual_matching_edge_excludes_false_twin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (x y z : V) (hxy : x ≠ y)
    (htwin : G.neighborSet x = G.neighborSet y) (hx : x ∈ R) (hz : z ∈ R)
    (hmatch : ∃ P : (G.induce {a | a ∈ R}).Subgraph, P.IsPerfectMatching)
    (hforced : ¬ ∃ P : ((G.induce {a | a ∈ R}).deleteEdges
      {s(⟨x,hx⟩,⟨z,hz⟩)}).Subgraph, P.IsPerfectMatching) : y ∉ R := by
  classical
  intro hy
  obtain ⟨P,hP⟩ := hmatch
  have hxz := perfect_matching_forced_edge_in_every_matching _ ⟨x,hx⟩ ⟨z,hz⟩ hforced P hP
  have hxy' : (⟨x,hx⟩ : {a : V // a ∈ R}) ≠ ⟨y,hy⟩ := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have htwin' : (G.induce {a | a ∈ R}).neighborSet ⟨x,hx⟩ =
      (G.induce {a | a ∈ R}).neighborSet ⟨y,hy⟩ := by
    ext a
    change G.Adj x a.val ↔ G.Adj y a.val
    exact Set.ext_iff.mp htwin a.val
  obtain ⟨Q,hQ,hno⟩ := perfect_matching_false_twins_switch_partner _ P hP _ _ _ hxy' htwin' hxz
  exact hno (perfect_matching_forced_edge_in_every_matching _ ⟨x,hx⟩ ⟨z,hz⟩ hforced Q hQ)
