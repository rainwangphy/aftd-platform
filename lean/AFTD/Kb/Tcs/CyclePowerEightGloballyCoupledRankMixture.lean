import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightPairwiseTightMixtureCounterexample

/-!
# cycle_power_eight_globally_coupled_rank_mixture

Topic: combinatorics   Node: 0dbc58a501af

Provenance: helper lemma. Global coupling for the explicit period-three relaxation in RT-1, experiment 27158.

For the explicit tight-class mixture, the displayed scenario maps are permutations and couple all three phases globally so that every dyadic-rank ownership equation holds in every scenario. Together with the previous mixture theorem, this shows that global rank consistency and averaged coverage and counts do not force equality of corrected counts.
-/

theorem cycle_power_eight_globally_coupled_rank_mixture :
  let f : Fin 3 → Fin 3 → Fin 3 := fun p s =>
    if p = 0 then s else if p = 1 then (![2,0,1] : Fin 3 → Fin 3) s
    else (![0,2,1] : Fin 3 → Fin 3) s
  (∀ p : Fin 3, Function.Injective (f p)) ∧
  (∀ v j s : Fin 3, (Finset.univ : Finset (Fin 3)).sum
    (fun p => rt1_mixture_owner865 v j p (f p s)) = 1) := by
  dsimp
  constructor <;> decide
