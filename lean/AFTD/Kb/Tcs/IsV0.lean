import AFTD.Prelude
import AFTD.Kb.Tcs.GammaVe

/-!
# is_v0

Topic: graphs   Node: bb9928b1c80f

Provenance: formalization of a published result. Source: arXiv:2610.26912 Section 1

A vertex v of a finite simple graph G belongs to V^0(G) if removing v preserves the vertex-edge domination number, that is, gamma_ve(G - v) = gamma_ve(G).
-/

/-- A vertex belongs to V^0(G) if removing it preserves the vertex-edge domination number. -/
def is_v0 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) : Prop := gamma_ve (G.induce ({v}ᶜ : Set V)) = gamma_ve G
