import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteLog

/-!
# power_residue_char

Topic: combinatorics   Node: 746ed2fca9bc

Provenance: formalization of a published result. Source: arXiv:2611.22205 Section 3

For natural numbers p and r and units g and x of (ZMod p)ˣ, power_residue_char p r g x is defined as the discrete logarithm discrete_log g x reduced modulo r in ZMod r.
-/

/-- Power-residue character χ(x) = ind_g(x) mod r on units modulo p. -/
noncomputable def power_residue_char (p r : ℕ) (g x : (ZMod p)ˣ) : ZMod r := (discrete_log g x : ZMod r)
