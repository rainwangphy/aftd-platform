import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsTwoThirdsConvex
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsSuperadditive
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameShapleyValue
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameCore
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameMarginalContrib
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsEfficient
import AFTD.Kb.GameTheoryEconomics.CoalitionalGamePayoffVector
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameCoalitionPayoff

/-!
# op_1641_two_thirds_convex_shapley_in_core_negation

Topic: general_equilibrium   Node: cf722c766682

Provenance: original. Related work: arXiv:2611.16207, Core nonemptiness for 2/3-convex games, Section 5

It is not the case that for every finite player set N with at least 3 players, the Shapley value of every superadditive 2/3-convex coalitional game on N belongs to its core.
-/

open Finset

def op_1641_v_int (S : Finset (Fin 3)) : ℤ :=
  if S = {0} then -4
  else if S = {2} then -1
  else if S = {1, 2} then -1
  else 0

lemma op_1641_v_int_empty : op_1641_v_int ∅ = 0 := by decide

def op_1641_v_real (S : Finset (Fin 3)) : ℝ := (op_1641_v_int S : ℝ)

lemma op_1641_v_real_empty : op_1641_v_real ∅ = 0 := by
  dsimp [op_1641_v_real]
  rw [op_1641_v_int_empty]
  push_cast
  rfl

def op_1641_G : CoalitionalGame (Fin 3) ℝ := {
  v := op_1641_v_real
  empty_zero := op_1641_v_real_empty
}

def op_1641_is_superadditive_int (v : Finset (Fin 3) → ℤ) : Prop :=
  ∀ S T : Finset (Fin 3), Disjoint S T → v (S ∪ T) ≥ v S + v T

def op_1641_is_two_thirds_convex_int (v : Finset (Fin 3) → ℤ) : Prop :=
  ∀ S₁ S₂ S₃ : Finset (Fin 3),
    S₁ ≠ S₂ → S₁ ≠ S₃ → S₂ ≠ S₃ →
      (v (S₁ ∪ S₂) + v (S₁ ∩ S₂) ≥ v S₁ + v S₂ ∧ v (S₁ ∪ S₃) + v (S₁ ∩ S₃) ≥ v S₁ + v S₃) ∨
      (v (S₁ ∪ S₂) + v (S₁ ∩ S₂) ≥ v S₁ + v S₂ ∧ v (S₂ ∪ S₃) + v (S₂ ∩ S₃) ≥ v S₂ + v S₃) ∨
      (v (S₁ ∪ S₃) + v (S₁ ∩ S₃) ≥ v S₁ + v S₃ ∧ v (S₂ ∪ S₃) + v (S₂ ∩ S₃) ≥ v S₂ + v S₃)

instance (v : Finset (Fin 3) → ℤ) : Decidable (op_1641_is_superadditive_int v) :=
  Fintype.decidableForallFintype

instance (v : Finset (Fin 3) → ℤ) : Decidable (op_1641_is_two_thirds_convex_int v) :=
  Fintype.decidableForallFintype

lemma op_1641_h_superadd_int : op_1641_is_superadditive_int op_1641_v_int := by decide
lemma op_1641_h_23_convex_int : op_1641_is_two_thirds_convex_int op_1641_v_int := by decide

lemma op_1641_G_superadd : op_1641_G.IsSuperadditive := by
  intro S T hST
  have := op_1641_h_superadd_int S T hST
  dsimp [op_1641_G, op_1641_v_real]
  exact_mod_cast this

lemma op_1641_G_two_thirds_convex : op_1641_G.IsTwoThirdsConvex := by
  intro S₁ S₂ S₃ h12 h13 h23
  have h_int := op_1641_h_23_convex_int S₁ S₂ S₃ h12 h13 h23
  dsimp [op_1641_G, op_1641_v_real]
  rcases h_int with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · left
    exact ⟨by exact_mod_cast hA, by exact_mod_cast hB⟩
  · right; left
    exact ⟨by exact_mod_cast hA, by exact_mod_cast hB⟩
  · right; right
    exact ⟨by exact_mod_cast hA, by exact_mod_cast hB⟩

lemma op_1641_v_0 : op_1641_G.v {0} = -4 := by
  have : op_1641_v_int {0} = -4 := by decide
  dsimp [op_1641_G, op_1641_v_real]; rw [this]; push_cast; rfl

lemma op_1641_v_empty : op_1641_G.v ∅ = 0 := by
  have : op_1641_v_int ∅ = 0 := by decide
  dsimp [op_1641_G, op_1641_v_real]; rw [this]; push_cast; rfl

lemma op_1641_v_01 : op_1641_G.v {0, 1} = 0 := by
  have : op_1641_v_int {0, 1} = 0 := by decide
  dsimp [op_1641_G, op_1641_v_real]; rw [this]; push_cast; rfl

lemma op_1641_v_1 : op_1641_G.v {1} = 0 := by
  have : op_1641_v_int {1} = 0 := by decide
  dsimp [op_1641_G, op_1641_v_real]; rw [this]; push_cast; rfl

lemma op_1641_v_02 : op_1641_G.v {0, 2} = 0 := by
  have : op_1641_v_int {0, 2} = 0 := by decide
  dsimp [op_1641_G, op_1641_v_real]; rw [this]; push_cast; rfl

lemma op_1641_v_2 : op_1641_G.v {2} = -1 := by
  have : op_1641_v_int {2} = -1 := by decide
  dsimp [op_1641_G, op_1641_v_real]; rw [this]; push_cast; rfl

lemma op_1641_v_012 : op_1641_G.v {0, 1, 2} = 0 := by
  have : op_1641_v_int {0, 1, 2} = 0 := by decide
  dsimp [op_1641_G, op_1641_v_real]; rw [this]; push_cast; rfl

lemma op_1641_v_12 : op_1641_G.v {1, 2} = -1 := by
  have : op_1641_v_int {1, 2} = -1 := by decide
  dsimp [op_1641_G, op_1641_v_real]; rw [this]; push_cast; rfl

lemma op_1641_G_shapley_0 : op_1641_G.shapleyValue 0 = -5 / 6 := by
  unfold CoalitionalGame.shapleyValue
  have hF : (filter (fun S : Finset (Fin 3) => (0 : Fin 3) ∉ S) univ) = {∅, {1}, {2}, {1, 2}} := by decide
  rw [hF]
  have h1 : (∅ : Finset (Fin 3)) ∉ ({ {1}, {2}, {1, 2} } : Finset (Finset (Fin 3))) := by decide
  have h2 : ({1} : Finset (Fin 3)) ∉ ({ {2}, {1, 2} } : Finset (Finset (Fin 3))) := by decide
  have h3 : ({2} : Finset (Fin 3)) ∉ ({ {1, 2} } : Finset (Finset (Fin 3))) := by decide
  rw [sum_insert h1, sum_insert h2, sum_insert h3, sum_singleton]
  unfold CoalitionalGame.marginalContrib
  have hc : Fintype.card (Fin 3) = 3 := by decide
  rw [hc]
  have ins0 : insert (0 : Fin 3) (∅ : Finset (Fin 3)) = {0} := by decide
  rw [ins0]
  have hc12 : (({1, 2} : Finset (Fin 3)).card) = 2 := by decide
  rw [hc12]
  norm_num
  rw [op_1641_v_0, op_1641_v_empty, op_1641_v_01, op_1641_v_1, op_1641_v_02, op_1641_v_2, op_1641_v_012, op_1641_v_12]
  norm_num

lemma op_1641_G_shapley_1 : op_1641_G.shapleyValue 1 = 2 / 3 := by
  unfold CoalitionalGame.shapleyValue
  have hF : (filter (fun S : Finset (Fin 3) => (1 : Fin 3) ∉ S) univ) = {∅, {0}, {2}, {0, 2}} := by decide
  rw [hF]
  have h1 : (∅ : Finset (Fin 3)) ∉ ({ {0}, {2}, {0, 2} } : Finset (Finset (Fin 3))) := by decide
  have h2 : ({0} : Finset (Fin 3)) ∉ ({ {2}, {0, 2} } : Finset (Finset (Fin 3))) := by decide
  have h3 : ({2} : Finset (Fin 3)) ∉ ({ {0, 2} } : Finset (Finset (Fin 3))) := by decide
  rw [sum_insert h1, sum_insert h2, sum_insert h3, sum_singleton]
  unfold CoalitionalGame.marginalContrib
  have hc : Fintype.card (Fin 3) = 3 := by decide
  rw [hc]
  have ins0 : insert (1 : Fin 3) (∅ : Finset (Fin 3)) = {1} := by decide
  have ins0_2 : insert (1 : Fin 3) ({0} : Finset (Fin 3)) = {0, 1} := by decide
  have ins2 : insert (1 : Fin 3) ({2} : Finset (Fin 3)) = {1, 2} := by decide
  have ins02 : insert (1 : Fin 3) ({0, 2} : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [ins0, ins0_2, ins2, ins02]
  have hc02 : (({0, 2} : Finset (Fin 3)).card) = 2 := by decide
  rw [hc02]
  norm_num
  rw [op_1641_v_0, op_1641_v_empty, op_1641_v_01, op_1641_v_1, op_1641_v_02, op_1641_v_2, op_1641_v_012, op_1641_v_12]
  norm_num

lemma op_1641_G_not_in_core : op_1641_G.shapleyValue ∉ op_1641_G.Core := by
  intro h
  have h_core := h.2 {0, 1}
  unfold CoalitionalGame.coalitionPayoff at h_core
  have h_disj : (0 : Fin 3) ∉ ({1} : Finset (Fin 3)) := by decide
  rw [sum_insert h_disj, sum_singleton] at h_core
  rw [op_1641_G_shapley_0, op_1641_G_shapley_1, op_1641_v_01] at h_core
  norm_num at h_core

/-- Refutation of OP-1641: the Shapley value of a superadditive 2/3-convex game need not belong to the core. -/
theorem op_1641_two_thirds_convex_shapley_in_core_negation :
    ¬ (∀ (N : Type) [Fintype N] [DecidableEq N] (G : CoalitionalGame N ℝ),
      3 ≤ Fintype.card N → G.IsSuperadditive → G.IsTwoThirdsConvex → G.shapleyValue ∈ G.Core) := by
  intro h
  have h_card : 3 ≤ Fintype.card (Fin 3) := by decide
  have h_in_core := h (Fin 3) op_1641_G h_card op_1641_G_superadd op_1641_G_two_thirds_convex
  exact op_1641_G_not_in_core h_in_core
