import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorNAEclause
import AFTD.Kb.Tcs.NAEtoColorClauseNodeColor
import AFTD.Kb.Tcs.NAEtoColorOutputVertex
import AFTD.Kb.Tcs.NAEtoColorSatisfiesClause
import AFTD.Kb.Tcs.NAEtoColorNaeColoring
import AFTD.Kb.Tcs.NAEtoColorNAESat3
import AFTD.Kb.Tcs.NAEtoColorReductionGraph
import AFTD.Kb.Tcs.NAEtoColorIsSatisfiable
import AFTD.Kb.Tcs.NAEtoColorEdgeRelation
import AFTD.Kb.Tcs.NAEtoColorIs3Colorable
import AFTD.Kb.Tcs.NAEtoColorSatisfiesNAE3

/-!
# NAEtoColor.NAEtoColorCompleteness

Topic: np_completeness   Node: 259531da26fc

Provenance: helper lemma. TCSlib, `NAEtoColor.NAEtoColorCompleteness`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Completeness of the NAE-SAT to 3-coloring reduction. Let $f$ be a NAE-SAT instance over a variable type $V$, that is, a list of not-all-equal
clauses each naming three variables. If $f$ is satisfiable — some Boolean assignment $V
\to \{\mathrm{true}, \mathrm{false}\}$ makes the three variables of every clause not all
receive the same value — then the reduction graph of $f$ is 3-colorable, meaning it
admits a proper coloring with the three colors $\{0, 1, 2\}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Completeness of reduction from NAE-SAT to 3-Coloring. -/
lemma NAEtoColor.NAEtoColorCompleteness {V : Type} (f : NAESat3 V) :
  IsSatisfiable f → Is3Colorable (ReductionGraph f) := by
  intro ⟨assign, hsat⟩
  refine ⟨⟨naeColoring assign, ?_⟩⟩
  intro u v hadj
  simp only [SimpleGraph.top_adj]
  obtain ⟨hne, hedge⟩ := hadj
  -- Prove for any directed edge; then handle both directions
  suffices ∀ {a b : OutputVertex V}, EdgeRelation f a b →
              naeColoring assign a ≠ naeColoring assign b by
    rcases hedge with h | h'
    · exact this h
    · exact fun heq => this h' heq.symm
  intro a b h
  match a, b with
  -- There are 6 cases to match:
  -- 1. Ground node : Ground node (no edge)
  | .groundNode, .groundNode => exact False.elim h
  -- 2. Ground node : Var node
  | .groundNode, .varNode v | .varNode v, .groundNode =>
      simp only [naeColoring]
      cases assign v <;> simp
  -- 3. Ground node : Clause node (no edge)
  | .groundNode, .clauseNode _ _ | .clauseNode _ _, .groundNode =>
    exact False.elim h
  -- 4. Var node : Var node (no edge)
  | .varNode v, .varNode w => exact False.elim h
  -- 5. Var node : Clause node
  | .varNode v, .clauseNode c k | .clauseNode c k, .varNode v =>
    simp only [EdgeRelation] at h
    simp only [naeColoring]
    -- After rcases, k is substituted to 0, 1, or 2 by the rfl
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (cases assign c.v0 <;> cases assign c.v1 <;> cases assign c.v2 <;>
       simp [clauseNodeColor])
  -- 6. Clause node : Clause node
  | .clauseNode c1 i, .clauseNode c2 j =>
    obtain ⟨rfl, hcIn, hij⟩ := h
    simp only [naeColoring]
    have hNAE : SatisfiesClause assign c1 = true :=
      List.all_eq_true.mp hsat c1 hcIn
    -- Case-split on both indices and all boolean assignments.
    -- Diagonal (i=j): hij gives contradiction. Non-diagonal non-NAE: hNAE gives contradiction.
    fin_cases i <;> fin_cases j <;>
      cases h0 : assign c1.v0 <;> cases h1 : assign c1.v1 <;> cases h2 : assign c1.v2 <;>
      simp_all [clauseNodeColor, SatisfiesClause]
