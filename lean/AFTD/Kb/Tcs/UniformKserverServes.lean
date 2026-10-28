import AFTD.Prelude

/-!
# uniform_kserver_serves

Topic: online_algorithms   Node: 89fb36fbf6b5

Provenance: formalization of a published result. Source: scout/2610-37192-tight-bounds-for-randomized-generalized-k-server-on-uniform.md:334

For a natural number k, a family of uniform metric spaces M indexed by Fin k, and configurations x, r in the product space over Fin k, x serves r if there exists an index i in Fin k such that x i = r i.
-/

/-- A server configuration serves a request if some server is at the requested point. -/
def uniform_kserver_serves {k : ℕ} {M : Fin k → Type*} (x r : ∀ i, M i) : Prop :=
  ∃ i : Fin k, x i = r i
