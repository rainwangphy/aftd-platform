import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.SignedGraphIsIsomorphic
import AFTD.Kb.Tcs.SignedGraphSwitch

/-!
# SignedGraph.SameDeck

Topic: combinatorics   Node: 8dee4226e2ed

Provenance: formalization of a published result. Source: arXiv:2611.13901, Sec. 2.2

Two signed graphs G1 and G2 on finite types V1 and V2 with decidable equality have the same switching deck if there exists an equivalence π : V1 ≃ V2 such that G1.switch v is isomorphic to G2.switch (π v) for all v.
-/

/-- Two signed graphs have the same switching deck if their vertex switchings are isomorphic via a bijection. -/
def SignedGraph.SameDeck {V1 V2 : Type*} [DecidableEq V1] [DecidableEq V2] [Fintype V1] [Fintype V2] (G1 : SignedGraph V1) (G2 : SignedGraph V2) : Prop :=
  ∃ (π : V1 ≃ V2), ∀ v : V1, SignedGraph.IsIsomorphic (G1.switch v) (G2.switch (π v))
