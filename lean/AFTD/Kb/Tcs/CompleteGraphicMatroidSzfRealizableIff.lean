import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteGraphicMatroidSzfRealizable
import AFTD.Kb.Tcs.NotCompleteGraphicMatroidSzfRealizableOfSixLe
import AFTD.Kb.Tcs.CompleteGraphicMatroidSzfRealizableOfLeFive

/-!
# complete_graphic_matroid_szf_realizable_iff

Topic: graphs   Node: 3194e12ccf28

Provenance: formalization of a published result. Source: arXiv:2611.15741 Theorem 4.5

For every integer n ≥ 1, the cycle matroid M(K_n) of the complete graph K_n is SZF-realizable (some multigraph on E(K_n), loops and parallel edges allowed, has skew zero forcing closure equal to the closure of M(K_n)) if and only if n ≤ 5.
-/

theorem complete_graphic_matroid_szf_realizable_iff (n : ℕ) (hn : 1 ≤ n) :
    complete_graphic_matroid_szf_realizable n ↔ n ≤ 5 := by
  constructor
  · intro h
    by_contra hgt
    have h6 : 6 ≤ n := by omega
    exact not_complete_graphic_matroid_szf_realizable_of_six_le n h6 h
  · intro h
    exact complete_graphic_matroid_szf_realizable_of_le_five n hn h
