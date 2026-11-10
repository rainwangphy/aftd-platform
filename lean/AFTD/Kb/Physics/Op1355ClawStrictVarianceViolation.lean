import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreWeightedVar
import AFTD.Kb.Physics.HardCoreWeightedClosedNeighborhoodBound

/-!
# op_1355_claw_strict_variance_violation

Topic: statistical_mechanics   Node: ee63295ee9c2

Provenance: formalization of a published result. Source: knowledgebase

On the complete bipartite claw graph completeBipartiteGraph (Fin 1) (Fin 3), there exist positive vertex fugacities lam and nonnegative observable weights a such that the weighted hard-core variance hardCoreWeightedVar is strictly less than the weighted closed-neighborhood bound hardCoreWeightedClosedNeighborhoodBound.
-/

open SimpleGraph
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

abbrev V702 := Fin 1 ⊕ Fin 3
abbrev G702 := completeBipartiteGraph (Fin 1) (Fin 3)
local instance : DecidableRel G702.Adj := fun v w => by
  change Decidable ((v.isLeft = true ∧ w.isRight = true) ∨
    (v.isRight = true ∧ w.isLeft = true))
  infer_instance
def c702 : V702 := Sum.inl 0
def l702 (i : Fin 3) : V702 := Sum.inr i
def lam702 : V702 → ℝ := fun v => match v with
  | Sum.inl _ => 1
  | Sum.inr _ => 100
def a702 : V702 → ℝ := fun v => match v with
  | Sum.inl _ => 1
  | Sum.inr _ => 0

def sets702 : Finset (Finset V702) :=
  {∅, {c702}, {l702 0}, {l702 1}, {l702 2},
   {l702 0, l702 1}, {l702 0, l702 2}, {l702 1, l702 2},
   {l702 0, l702 1, l702 2}}

lemma indeps702 : ({I | G702.IsIndepSet (↑I : Set V702)} : Finset (Finset V702)) = sets702 := by
  decide

lemma var702 : hardCoreWeightedVar G702 lam702 a702 = (1 : ℝ) / 1030302 - (1 / 1030302)^2 := by
  classical
  unfold hardCoreWeightedVar
  rw [indeps702]
  simp (disch := decide) [sets702, c702, l702, lam702, a702,
    Finset.sum_insert, Finset.prod_insert]
  <;> norm_num

lemma bound702 : hardCoreWeightedClosedNeighborhoodBound G702 lam702 a702 = (1 : ℝ) / 91204 := by
  classical
  have hneigh : G702.neighborFinset (Sum.inl 0) = {Sum.inr 0, Sum.inr 1, Sum.inr 2} := by
    ext v
    cases v with
    | inl x => fin_cases x <;> simp [SimpleGraph.mem_neighborFinset, completeBipartiteGraph]
    | inr x => fin_cases x <;> simp [SimpleGraph.mem_neighborFinset, completeBipartiteGraph]
  simp (disch := decide) [hardCoreWeightedClosedNeighborhoodBound, lam702, a702,
    Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_zero, hneigh,
    Finset.sum_insert]
  <;> norm_num

/-- The claw graph K_{1,3} strictly violates the weighted hard-core closed-neighborhood variance bound for suitable positive fugacities and nonnegative observable weights. -/
theorem op_1355_claw_strict_variance_violation :
    ∃ (lam : Fin 1 ⊕ Fin 3 → ℝ) (hlam : ∀ v, 0 < lam v) (a : Fin 1 ⊕ Fin 3 → ℝ) (ha : ∀ v, 0 ≤ a v),
      hardCoreWeightedVar (completeBipartiteGraph (Fin 1) (Fin 3)) lam a <
        hardCoreWeightedClosedNeighborhoodBound (completeBipartiteGraph (Fin 1) (Fin 3)) lam a := by
  refine ⟨lam702, ?_, a702, ?_, ?_⟩
  · intro v; cases v <;> norm_num [lam702]
  · intro v; cases v <;> norm_num [a702]
  · rw [var702, bound702]; norm_num
