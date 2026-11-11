import AFTD.Prelude
import AFTD.Kb.Tcs.IsConnectedForcingSet

/-!
# connected_forcing_poly

Topic: graphs   Node: ca2dc0749066

Provenance: formalization of a published result. Source: arXiv:2611.11352 Section 1

Given a finite type V and a simple graph G on V, connected_forcing_poly G is the polynomial in Polynomial ℕ defined as the sum over all subsets S : Finset V of (if is_connected_forcing_set G (S : Set V) then Polynomial.X ^ S.card else 0).
-/

/-- Connected forcing polynomial of a graph. -/
noncomputable def connected_forcing_poly {V : Type*} [Fintype V] (G : SimpleGraph V) : Polynomial ℕ := open scoped Classical in
  ∑ S : Finset V, if is_connected_forcing_set G (S : Set V) then Polynomial.X ^ S.card else 0
