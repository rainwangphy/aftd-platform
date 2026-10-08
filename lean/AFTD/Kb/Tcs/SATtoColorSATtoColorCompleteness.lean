import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorEdgeRelation
import AFTD.Kb.Tcs.SATtoColorSat3ColoringLitNode
import AFTD.Kb.Tcs.SATtoColorOutputVertex
import AFTD.Kb.Tcs.SATtoColorIsSatisfiable
import AFTD.Kb.Tcs.SATtoColorLiteral
import AFTD.Kb.Tcs.SATtoColorIs3Colorable
import AFTD.Kb.Tcs.SATtoColorSatisfiesClause
import AFTD.Kb.Tcs.SATtoColorSatisfiesLiteral
import AFTD.Kb.Tcs.SATtoColorClause
import AFTD.Kb.Tcs.SATtoColorReductionGraph
import AFTD.Kb.Tcs.SATtoColorSat3
import AFTD.Kb.Tcs.SATtoColorClauseGadgetColor
import AFTD.Kb.Tcs.SATtoColorSat3Coloring
import AFTD.Kb.Tcs.SATtoColorSatisfiesSat3

/-!
# SATtoColor.SATtoColorCompleteness

Topic: np_completeness   Node: 909d3ad128dc

Provenance: helper lemma. TCSlib, `SATtoColor.SATtoColorCompleteness`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Completeness of the 3-SAT to 3-coloring reduction. Let $f$ be a 3-SAT instance over a variable type $V$, that is, a list of clauses, each a
disjunction of three literals. If $f$ is satisfiable — there exists a Boolean assignment
$\mathrm{assign} : V \to \mathrm{Bool}$ under which every clause of $f$ has at least one
true literal — then the reduction graph $\mathrm{ReductionGraph}(f)$ is 3-colorable,
i.e.\ it admits a proper coloring by the three colors $\mathrm{Fin}\,3$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Completeness of reduction from 3-SAT to 3-Coloring. -/
lemma SATtoColor.SATtoColorCompleteness {V : Type} (f : Sat3 V) :
  IsSatisfiable f → Is3Colorable (ReductionGraph f) := by
  intro ⟨assign, hsat⟩
  refine ⟨⟨sat3Coloring assign, ?_⟩⟩
  intro u v hadj
  simp only [SimpleGraph.top_adj]
  obtain ⟨hne, hedge⟩ := hadj
  suffices key : ∀ {a b : OutputVertex V}, EdgeRelation f a b →
                   sat3Coloring assign a ≠ sat3Coloring assign b by
    rcases hedge with h | h
    · exact key h
    · exact fun heq => key h heq.symm
  intro a b h
  cases a with
  | palette i =>
    cases b with
    | palette j =>
      simp only [sat3Coloring]
      simp only [EdgeRelation] at h
      exact h
    | literalNode l =>
      fin_cases i
      · rw [sat3Coloring_litNode]; simp only [sat3Coloring]
        cases SatisfiesLiteral assign l <;> simp
      · exact absurd h (by simp [EdgeRelation])
      · exact absurd h (by simp [EdgeRelation])
    | clauseGadget c k =>
      fin_cases i <;> fin_cases k <;>
        simp_all [EdgeRelation, sat3Coloring, clauseGadgetColor]
  | literalNode l =>
    cases b with
    | palette j =>
      fin_cases j
      · rw [sat3Coloring_litNode]; simp only [sat3Coloring]
        cases SatisfiesLiteral assign l <;> simp
      · exact absurd h (by simp [EdgeRelation])
      · exact absurd h (by simp [EdgeRelation])
    | literalNode l2 =>
      cases l with
      | pos x =>
        cases l2 with
        | pos y => exact absurd h (by simp [EdgeRelation])
        | neg y =>
          simp only [EdgeRelation] at h
          simp only [sat3Coloring]; subst h
          cases assign x <;> simp
      | neg x =>
        cases l2 with
        | neg y => exact absurd h (by simp [EdgeRelation])
        | pos y =>
          simp only [EdgeRelation] at h
          simp only [sat3Coloring]; subst h
          cases assign x <;> simp
    | clauseGadget c k =>
      simp only [EdgeRelation] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (
        rw [sat3Coloring_litNode]; simp only [sat3Coloring]
        cases hA : SatisfiesLiteral assign c.l1 <;>
        cases hB : SatisfiesLiteral assign c.l2 <;>
        cases hC : SatisfiesLiteral assign c.l3 <;>
        simp [clauseGadgetColor])
  | clauseGadget c k =>
    cases b with
    | palette j =>
      fin_cases j <;> fin_cases k <;>
        simp_all [EdgeRelation, sat3Coloring, clauseGadgetColor]
    | literalNode l =>
      simp only [EdgeRelation] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (
        rw [sat3Coloring_litNode]; simp only [sat3Coloring]
        cases hA : SatisfiesLiteral assign c.l1 <;>
        cases hB : SatisfiesLiteral assign c.l2 <;>
        cases hC : SatisfiesLiteral assign c.l3 <;>
        simp [clauseGadgetColor])
    | clauseGadget c2 j =>
      simp only [EdgeRelation] at h
      obtain ⟨rfl, hcIn, hidx⟩ := h
      simp only [sat3Coloring]
      have hClauseTrue : SatisfiesClause assign c = true :=
        List.all_eq_true.mp hsat c hcIn
      rcases hidx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (
        cases hA : SatisfiesLiteral assign c.l1 <;>
        cases hB : SatisfiesLiteral assign c.l2 <;>
        cases hC : SatisfiesLiteral assign c.l3 <;>
        simp_all [clauseGadgetColor, SatisfiesClause])
