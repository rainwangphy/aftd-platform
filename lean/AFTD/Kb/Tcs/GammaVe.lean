import AFTD.Prelude
import AFTD.Kb.Tcs.IsVeDominating

/-!
# gamma_ve

Topic: graphs   Node: c70b58470d47

Provenance: formalization of a published result. Source: arXiv:2610.26912 Section 1

The vertex-edge domination number gamma_ve(G) of a finite simple graph G is the minimum cardinality of a finite subset S of V that is a vertex-edge dominating set of G.
-/

/-- The vertex-edge domination number gamma_ve(G) is the minimum cardinality of a ve-dominating set of G. -/
noncomputable def gamma_ve {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := sInf {k : ℕ | ∃ S : Finset V, is_ve_dominating G (S : Set V) ∧ S.card = k}
