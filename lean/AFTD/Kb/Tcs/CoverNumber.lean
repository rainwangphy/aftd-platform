import AFTD.Prelude
import AFTD.Kb.Tcs.IsMonochromaticCover

/-!
# cover_number

Topic: communication   Node: fec8dc7e122f

Provenance: formalization of a published result. Source: arXiv:2611.11488, Section 1.1

The $b$-monochromatic cover number $\mathrm{cover\_number}(f, b)$ of a curried Boolean function $f : X \to Y \to \mathrm{Bool}$ is the extended natural number in $\mathrm{ENat}$ defined as the infimum of $C.\mathrm{encard}$ over all collections $C : \mathrm{Set}\;(\mathrm{Set}\;(X \times Y))$ satisfying $\mathrm{is\_monochromatic\_cover}\;C\;f\;b$.
-/

/-- The minimum number of b-monochromatic rectangles needed to cover f⁻¹(b). -/
noncomputable def cover_number {X Y : Type*} (f : X → Y → Bool) (b : Bool) : ENat := ⨅ (C : Set (Set (X × Y))) (_ : is_monochromatic_cover C f b), C.encard
