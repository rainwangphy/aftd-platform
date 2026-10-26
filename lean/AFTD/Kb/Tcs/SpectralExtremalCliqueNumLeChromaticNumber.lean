import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralExtremalCliqueNum
import AFTD.Kb.Tcs.SpectralExtremalChromaticNumber
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.AdjacencySpectralRadius

/-!
# spectral_extremal_clique_num_le_chromatic_number

Topic: graphs   Node: f446ddcb55a3

Provenance: formalization of a published result. Source: arXiv:2610.13852 Sec. 6, Eq. (6.1)

For every natural number k and real number r, the extremal distance-k clique number spectral_extremal_clique_num k r is less than or equal to the extremal distance-k chromatic number spectral_extremal_chromatic_number k r.
-/

/-- For every natural number k and real number r, the extremal distance-k clique number is at most the extremal distance-k chromatic number. -/
theorem spectral_extremal_clique_num_le_chromatic_number (k : ℕ) (r : ℝ) :
    spectral_extremal_clique_num k r ≤ spectral_extremal_chromatic_number k r := by
  unfold spectral_extremal_clique_num spectral_extremal_chromatic_number
  exact iSup_mono fun n => iSup_mono fun G => iSup_mono fun _ => SimpleGraph.cliqueNum_le_chromaticNumber
