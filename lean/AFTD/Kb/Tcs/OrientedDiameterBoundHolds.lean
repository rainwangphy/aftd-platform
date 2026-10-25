import AFTD.Prelude
import AFTD.Kb.Tcs.HasStrongOrientationOfDiameterLe

/-!
# oriented_diameter_bound_holds

Topic: graphs   Node: 8a6393331d7c

Provenance: formalization of a published result. Source: arXiv:2610.09648 (An asymptotically tight bound on oriented diameter), Section 1: the function f(d), the smallest integer such that every finite connected bridgeless simple graph of diameter d admits a strong orientation of diameter at most f(d); f(d) <= k iff this predicate holds.

oriented_diameter_bound_holds d k: every finite connected bridgeless simple graph of diameter d (taken on vertex set Fin n, which loses nothing) has a strong orientation of directed diameter at most k. In the paper's notation this says f(d) <= k, where f(d) is the smallest such k.
-/

def oriented_diameter_bound_holds (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected → (∀ e, ¬ G.IsBridge e) → G.diam = d →
    has_strong_orientation_of_diameter_le G k
