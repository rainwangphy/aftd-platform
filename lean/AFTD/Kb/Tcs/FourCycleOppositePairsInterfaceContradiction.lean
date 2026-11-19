import AFTD.Prelude

/-!
# four_cycle_opposite_pairs_interface_contradiction

Topic: combinatorics   Node: 561bbb99494d

Provenance: helper lemma. Palette obstruction reduction for the OP-874 campaign.

The opposite-pair and exposed-port conditions on a four-cycle are inconsistent.
-/

theorem four_cycle_opposite_pairs_interface_contradiction
    {Ω : Type*} (p q r s d u v : Ω)
    (hu : u = p ∨ u = s) (hup : u ≠ p) (huq : u ≠ q)
    (hv : v = q ∨ v = r) (hvp : v ≠ p) (hvq : v ≠ q)
    (hd1 : d = p ∨ d = q) (hd2 : d = r ∨ d = s) : False := by
  have hus : u = s := hu.resolve_left hup
  have hvr : v = r := hv.resolve_left hvq
  rcases hd1 with hp | hq <;> rcases hd2 with hr | hs
  · exact hvp (hvr.trans (hr.symm.trans hp))
  · exact hup (hus.trans (hs.symm.trans hp))
  · exact hvq (hvr.trans (hr.symm.trans hq))
  · exact huq (hus.trans (hs.symm.trans hq))
