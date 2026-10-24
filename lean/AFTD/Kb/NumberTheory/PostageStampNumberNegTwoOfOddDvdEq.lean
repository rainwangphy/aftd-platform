import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_number_neg_two_of_odd_dvd_eq

Topic: elementary_number_theory   Node: 00cbe8480d84

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

If 0 < N, N ∣ D and 0 < D < 2N, then D = N.
-/

theorem postage_stamp_number_neg_two_of_odd_dvd_eq (N D : ℤ) (hN : 0 < N) (hd : N ∣ D)
    (h1 : 0 < D) (h2 : D < 2 * N) : D = N := by
  obtain ⟨c, rfl⟩ := hd
  have hc1 : 0 < c := by
    by_contra h; push Not at h; nlinarith
  have hc2 : c < 2 := by
    by_contra h; push Not at h; nlinarith
  have : c = 1 := by omega
  subst this; ring
