import AFTD.Prelude

/-!
# good_slopes_point_directions

Topic: elementary_number_theory   Node: 9ac7cdc1cbbe

Provenance: helper lemma. Point-fiber directions for the CRT approach to OP-1027; compare arXiv:2611.04551, Section 9.

The unit directions a for which the linear form y + a x is injective on a finite set of points over the residues modulo n.
-/

noncomputable def good_slopes_point_directions (n : ℕ) [NeZero n] (S : Finset (ZMod n × ZMod n)) : Finset (ZMod n) := by
  classical
  exact Finset.univ.filter fun a => IsUnit a ∧ Set.InjOn (fun p : ZMod n × ZMod n => p.2 + a * p.1) S
