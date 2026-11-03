import AFTD.Prelude

/-!
# circulant_1_3

Topic: graphs   Node: e126758a2e06

Provenance: formalization of a published result. Source: arXiv:2610.41820 Section 1

The 4-regular circulant graph C_n(1,3) on vertex set ZMod n with connection set {1, -1, 3, -3}.
-/

/-- The 4-regular circulant graph C_n(1,3) on ZMod n with jump set {1, -1, 3, -3}. -/
noncomputable def circulant_1_3 (n : ℕ) : SimpleGraph (ZMod n) := SimpleGraph.circulantGraph ({1, -1, 3, -3} : Set (ZMod n))
