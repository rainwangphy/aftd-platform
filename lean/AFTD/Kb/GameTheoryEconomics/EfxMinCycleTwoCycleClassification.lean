import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleChampion
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleSubset
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleGoods
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxMinCyclePartialEfx

/-!
# efx_min_cycle_two_cycle_classification

Topic: fair_division   Node: 8f610a654d66

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

Every inclusion-minimal two-cycle is the pair of agents 0 and 1, with target-0 set {0,1,12} and target-1 set either {3,4,12} or {4,5,12}. The Boolean masks cover every subset by efx_min_cycle_subset_complete.
-/

/-- Exhaustive classification of the possible champions (a finite kernel check). -/
private lemma efx_min_cycle_two_cycle_classification_enum (i j : Fin 4) (b : Fin 4 → Bool)
    (h : efx_min_cycle_champion i j (efx_min_cycle_subset j b)) :
    (i = 0 ∧ j = 1 ∧ (efx_min_cycle_subset j b = {3,4,12} ∨ efx_min_cycle_subset j b = {4,5,12})) ∨
    (i = 0 ∧ j = 2 ∧ efx_min_cycle_subset j b = {8,12}) ∨
    (i = 0 ∧ j = 3 ∧ efx_min_cycle_subset j b = {9,12}) ∨
    (i = 1 ∧ j = 0 ∧ efx_min_cycle_subset j b = {0,1,12}) ∨
    (i = 1 ∧ j = 2 ∧ efx_min_cycle_subset j b = {6,12}) ∨
    (i = 1 ∧ j = 3 ∧ efx_min_cycle_subset j b = {11,12}) := by
  revert i j b
  unfold efx_min_cycle_champion efx_min_cycle_subset
  decide

/-- Two mutual champions can only be the pair of agents 0 and 1. -/
private lemma efx_min_cycle_two_cycle_classification_pair (i j : Fin 4) (b c : Fin 4 → Bool)
    (_hij : i ≠ j)
    (hijc : efx_min_cycle_champion i j (efx_min_cycle_subset j b))
    (hjic : efx_min_cycle_champion j i (efx_min_cycle_subset i c)) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  have h1 := efx_min_cycle_two_cycle_classification_enum i j b hijc
  have h2 := efx_min_cycle_two_cycle_classification_enum j i c hjic
  rcases h1 with ⟨a1, b1, _⟩ | ⟨a1, b1, _⟩ | ⟨a1, b1, _⟩ | ⟨a1, b1, _⟩ | ⟨a1, b1, _⟩ | ⟨a1, b1, _⟩ <;>
    rcases h2 with ⟨a2, b2, _⟩ | ⟨a2, b2, _⟩ | ⟨a2, b2, _⟩ | ⟨a2, b2, _⟩ | ⟨a2, b2, _⟩ | ⟨a2, b2, _⟩ <;>
    omega

/-- The only champions of agent 0 against old bundle 1 are `{3,4,12}` and `{4,5,12}`. -/
private lemma efx_min_cycle_two_cycle_classification_target01 (b : Fin 4 → Bool)
    (h : efx_min_cycle_champion 0 1 (efx_min_cycle_subset 1 b)) :
    efx_min_cycle_subset 1 b = {3,4,12} ∨ efx_min_cycle_subset 1 b = {4,5,12} := by
  revert b
  unfold efx_min_cycle_champion efx_min_cycle_subset
  decide

/-- The only champion of agent 1 against old bundle 0 is `{0,1,12}`. -/
private lemma efx_min_cycle_two_cycle_classification_target10 (b : Fin 4 → Bool)
    (h : efx_min_cycle_champion 1 0 (efx_min_cycle_subset 0 b)) :
    efx_min_cycle_subset 0 b = {0,1,12} := by
  revert b
  unfold efx_min_cycle_champion efx_min_cycle_subset
  decide

theorem efx_min_cycle_two_cycle_classification (i j : Fin 4) (b c : Fin 4 → Bool)
  (hij : i ≠ j)
  (hijc : efx_min_cycle_champion i j (efx_min_cycle_subset j b))
  (hjic : efx_min_cycle_champion j i (efx_min_cycle_subset i c)) :
  (i = 0 ∧ j = 1 ∧
    (efx_min_cycle_subset j b = {3,4,12} ∨ efx_min_cycle_subset j b = {4,5,12}) ∧
    efx_min_cycle_subset i c = {0,1,12}) ∨
  (i = 1 ∧ j = 0 ∧ efx_min_cycle_subset j b = {0,1,12} ∧
    (efx_min_cycle_subset i c = {3,4,12} ∨ efx_min_cycle_subset i c = {4,5,12})) := by
  rcases efx_min_cycle_two_cycle_classification_pair i j b c hij hijc hjic with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, efx_min_cycle_two_cycle_classification_target01 b hijc,
      efx_min_cycle_two_cycle_classification_target10 c hjic⟩
  · exact Or.inr ⟨rfl, rfl, efx_min_cycle_two_cycle_classification_target10 b hijc,
      efx_min_cycle_two_cycle_classification_target01 c hjic⟩
