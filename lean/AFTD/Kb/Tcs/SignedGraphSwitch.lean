import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph

/-!
# SignedGraph.switch

Topic: combinatorics   Node: 4915cc77439a

Provenance: formalization of a published result. Source: arXiv:2611.13901, Sec. 2.1

The switching of a signed graph G at a vertex v is the signed graph with the same underlying graph where the sign of every edge incident to v is negated and all other edge signs remain unchanged.
-/

/-- Switching a signed graph at a vertex negates the signs of incident edges. -/
def SignedGraph.switch {V : Type*} [DecidableEq V] (G : SignedGraph V) (v : V) : SignedGraph V where
  graph := G.graph
  sgn e := if (v ∈ (e : Sym2 V)) then - G.sgn e else G.sgn e
  sgn_mem := by
    intro e
    split_ifs
    · rcases G.sgn_mem e with h | h
      · right; omega
      · left; omega
    · exact G.sgn_mem e
