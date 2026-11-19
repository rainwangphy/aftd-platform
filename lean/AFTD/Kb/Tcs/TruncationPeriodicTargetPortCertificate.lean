import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationPeriodicFactorColor
import AFTD.Kb.Tcs.TruncationPeriodicMatchingBit
import AFTD.Kb.Tcs.TruncationPeriodicOtherBit
import AFTD.Kb.Tcs.TruncationPeriodicPreviousPort
import AFTD.Kb.Tcs.TruncationPeriodicNextPort
import AFTD.Kb.Tcs.TruncationPeriodicAuxiliaryExposure

/-!
# truncation_periodic_target_port_certificate

Topic: graphs   Node: 72b55e069c81

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The specified periodic target states use six different colors and have pairwise compatible target and auxiliary ports.
-/

theorem truncation_periodic_target_port_certificate :
    ∀ i : Fin 4,
      ({truncation_periodic_matching_bit i, truncation_periodic_other_bit i,
        truncation_periodic_factor_color (i-1), truncation_periodic_factor_color i,
        truncation_periodic_previous_port i, truncation_periodic_next_port i} : Finset (Fin 6)).card = 6 ∧
      Disjoint ({truncation_periodic_other_bit i, truncation_periodic_previous_port i} : Finset (Fin 6))
        {truncation_periodic_other_bit (i+1), truncation_periodic_next_port (i+1)} ∧
      Disjoint ({truncation_periodic_previous_port i, truncation_periodic_next_port i} : Finset (Fin 6))
        {truncation_periodic_other_bit i, truncation_periodic_auxiliary_exposure i} := by
  decide
