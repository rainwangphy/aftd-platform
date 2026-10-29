import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Hunger3Fire
import AFTD.Kb.GameTheoryEconomics.HungerFiringState
import AFTD.Kb.GameTheoryEconomics.HungerStep

/-!
# hunger3_firing_cell

Topic: combinatorial_games   Node: dbe835659b12

Provenance: helper lemma. step towards symmetric_hunger_tile_convex_iff_ultrametric_transition_three

For a real 3-by-3 matrix Q and a permutation e, hunger3_firing_cell Q e is the topological closure (in Fin 3 → ℝ) of the set of zero-sum vectors whose hunger dynamics fires e 0, then e 1, then e 2.
-/

/-- The closure of the set of zero-sum states whose three firing states are, in order, e 0, e 1, e 2. -/
noncomputable def hunger3_firing_cell (Q : Matrix (Fin 3) (Fin 3) ℝ) (e : Equiv.Perm (Fin 3)) : Set (Fin 3 → ℝ) := closure {h | (∑ i, h i = 0) ∧ hunger_firing_state h = e 0 ∧
    hunger_firing_state (hunger_step Q h) = e 1 ∧
    hunger_firing_state (hunger_step Q (hunger_step Q h)) = e 2}
