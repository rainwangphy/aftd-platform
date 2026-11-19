import AFTD.Prelude

/-!
# PlaneEmbedding

Topic: graphs   Node: 652d060608c0

Provenance: formalization of a published result. Source: scout/2611-23164-determining-compatible-groups-in-gamma-zonal-labelings.md:99

A plane embedding of a simple graph G represented by a rotation system (a permutation of darts whose cycles correspond to the cyclic order of edges around each vertex) satisfying Euler's spherical formula V - E + F = 2.
-/

/-- A rotation-system plane embedding of a simple graph G satisfying Euler's formula for the sphere. -/
structure PlaneEmbedding {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] where
  rot : Equiv.Perm G.Dart
  rot_fst : ∀ d : G.Dart, (rot d).fst = d.fst
  sameCycle_iff_fst_eq : ∀ d₁ d₂ : G.Dart, rot.SameCycle d₁ d₂ ↔ d₁.fst = d₂.fst
  euler_spherical : (Fintype.card V : ℤ) - ((Fintype.card G.Dart : ℤ) / 2) +
    (Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (Equiv.mk (fun d => rot d.symm) (fun d => (rot.symm d).symm) (by intro; simp) (by intro; simp)))) : ℤ) = 2
