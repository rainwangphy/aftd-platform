import AFTD.Prelude
import AFTD.Kb.Tcs.IsMonochromaticCoverAll

/-!
# cover_number_all

Topic: communication   Node: 1de9e6ee8293

Provenance: formalization of a published result. Source: arXiv:2611.11488, Section 1.1

The all-inputs monochromatic cover number $\mathrm{cover\_number\_all}(f)$ of a curried Boolean function $f : X \to Y \to \mathrm{Bool}$ is the extended natural number in $\mathrm{ENat}$ defined as the infimum of $C.\mathrm{encard}$ over all collections $C : \mathrm{Set}\;(\mathrm{Set}\;(X \times Y))$ satisfying $\mathrm{is\_monochromatic\_cover\_all}\;C\;f$.
-/

/-- The minimum number of monochromatic rectangles of either color covering all inputs. -/
noncomputable def cover_number_all {X Y : Type*} (f : X → Y → Bool) : ENat := ⨅ (C : Set (Set (X × Y))) (_ : is_monochromatic_cover_all C f), C.encard
