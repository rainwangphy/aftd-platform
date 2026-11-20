import AFTD.Prelude

/-!
# ssss_cuts

Topic: lp_duality   Node: 66cb22a95132

Provenance: formalization of a published result. Source: arXiv:2611.26188, Section 3

For a finite vertex set V and vertices s, t ∈ V, ssss_cuts s t is the set of all non-empty subsets of V \ {s, t}.
-/

/-- The collection of non-empty subsets of V \ {s, t}, indexing cut constraints in SSSS multi-path TSP. -/
def ssss_cuts {V : Type*} [Fintype V] [DecidableEq V] (s t : V) : Finset (Finset V) := (Finset.powerset (Finset.univ \ {s, t})).filter Finset.Nonempty
