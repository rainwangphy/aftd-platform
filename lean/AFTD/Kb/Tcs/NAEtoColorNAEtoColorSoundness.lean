import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorEdgeRelation
import AFTD.Kb.Tcs.NAEtoColorIs3Colorable
import AFTD.Kb.Tcs.NAEtoColorIsSatisfiable
import AFTD.Kb.Tcs.NAEtoColorNAESat3
import AFTD.Kb.Tcs.NAEtoColorNAEclause
import AFTD.Kb.Tcs.NAEtoColorOutputVertex
import AFTD.Kb.Tcs.NAEtoColorReductionGraph
import AFTD.Kb.Tcs.NAEtoColorSatisfiesClause
import AFTD.Kb.Tcs.NAEtoColorSatisfiesNAE3
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.G

/-!
# NAEtoColor.NAEtoColorSoundness

Topic: np_completeness   Node: 3c8cb845b879

Provenance: helper lemma. TCSlib, `NAEtoColor.NAEtoColorSoundness`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Soundness of the NAE-SAT to 3-coloring reduction. Let $f$ be a NAE-SAT instance over a variable type $V$, that is, a list of Not-All-Equal
clauses, each clause naming three variables. Form the reduction graph associated to $f$:
its vertices are a single ground vertex, one vertex for each variable in $V$, and, for
every clause, three gadget vertices; its edges join the ground vertex to each variable
vertex, join each variable vertex $v$ to a clause-gadget vertex whenever $v$ occurs in
the corresponding position of that clause, and, for every clause of $f$, join its three
gadget vertices pairwise into a triangle. If this graph is 3-colorable — that is, its
vertices admit a coloring by $\{0,1,2\}$ in which adjacent vertices receive distinct
colors — then $f$ is satisfiable: there exists a Boolean assignment $\mathit{assign} : V
\to \{\mathrm{true},\mathrm{false}\}$ under which every clause of $f$ has its three
assigned values not all equal.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Soundness of reduction from NAE-SAT to 3-Coloring. -/
lemma NAEtoColor.NAEtoColorSoundness {V : Type} (f : NAESat3 V) :
  Is3Colorable (ReductionGraph f) → IsSatisfiable f := by
  intro ⟨⟨col, hcol⟩⟩
  simp only [SimpleGraph.top_adj] at hcol
  have colNe : ∀ {u v : OutputVertex V},
      u ≠ v → (EdgeRelation f u v ∨ EdgeRelation f v u) → col u ≠ col v :=
    fun hne hedge => hcol ⟨hne, hedge⟩
  -- Variables differ from ground
  have hVG : ∀ v : V, col (.varNode v) ≠ col .groundNode := fun v =>
    colNe (by simp) (Or.inl trivial)
  -- Clause nodes in same clause are pairwise distinct (triangle)
  have hCC : ∀ (c : NAEclause V), c ∈ f → ∀ (i j : Fin 3), i ≠ j →
      col (.clauseNode c i) ≠ col (.clauseNode c j) := fun c hcIn i j hij =>
    colNe (by simp [hij]) (Or.inl ⟨rfl, hcIn, hij⟩)
  -- Each clause node differs from its variable (using tactic to unfold EdgeRelation)
  have hVC0 : ∀ c : NAEclause V, col (.clauseNode c 0) ≠ col (.varNode c.v0) := fun c =>
    Ne.symm (colNe (by simp) (by left; left; exact ⟨rfl, rfl⟩))
  have hVC1 : ∀ c : NAEclause V, col (.clauseNode c 1) ≠ col (.varNode c.v1) := fun c =>
    Ne.symm (colNe (by simp) (by left; right; left; exact ⟨rfl, rfl⟩))
  have hVC2 : ∀ c : NAEclause V, col (.clauseNode c 2) ≠ col (.varNode c.v2) := fun c =>
    Ne.symm (colNe (by simp) (by left; right; right; exact ⟨rfl, rfl⟩))
  -- Define: True color = groundColor + 1 (mod 3); assign v = True iff varNode has that color
  let cTrue : Fin 3 := col .groundNode + 1
  let assign v := decide (col (.varNode v) = cTrue)
  refine ⟨assign, ?_⟩
  simp only [SatisfiesNAE3, List.all_eq_true]
  intro c hcIn
  by_contra hFalse
  -- NAE violated → all three variables have the same boolean assignment value
  have hSatF : SatisfiesClause assign c = false := by
    rcases Bool.eq_false_or_eq_true (SatisfiesClause assign c) with h | h
    · exact absurd h hFalse  -- h : ... = true, hFalse : ¬... = true → absurd
    · exact h                -- h : ... = false
  simp only [SatisfiesClause] at hSatF
  -- Extract: all three assign values are equal
  have hall : assign c.v0 = assign c.v1 ∧ assign c.v0 = assign c.v2 := by
    constructor <;>
      (cases h0 : assign c.v0 <;> cases h1 : assign c.v1 <;> cases h2 : assign c.v2 <;>
       simp_all)
  obtain ⟨h01, h02⟩ := hall
  -- In both cases (all true / all false), all three varNodes have the same Fin 3 color
  have hSameColor : col (.varNode c.v0) = col (.varNode c.v1) ∧
                    col (.varNode c.v0) = col (.varNode c.v2) := by
    cases hb : assign c.v0 with
    | true =>
      -- All true: all varNodes have color cTrue → directly equal
      have ht0 : col (.varNode c.v0) = cTrue := of_decide_eq_true hb
      have ht1 : col (.varNode c.v1) = cTrue := of_decide_eq_true (h01.symm.trans hb)
      have ht2 : col (.varNode c.v2) = cTrue := of_decide_eq_true (h02.symm.trans hb)
      exact ⟨ht0.trans ht1.symm, ht0.trans ht2.symm⟩
    | false =>
      -- All false: varNodes ≠ cTrue and ≠ ground → unique remaining color in Fin 3
      have hf0 : col (.varNode c.v0) ≠ cTrue := of_decide_eq_false hb
      have hf1 : col (.varNode c.v1) ≠ cTrue := of_decide_eq_false (h01.symm.trans hb)
      have hf2 : col (.varNode c.v2) ≠ cTrue := of_decide_eq_false (h02.symm.trans hb)
      have hg0 := hVG c.v0; have hg1 := hVG c.v1; have hg2 := hVG c.v2
      -- cTrue ≠ groundNode color (adding 1 in Fin 3 is always a change)
      have hcTneG : cTrue.val ≠ (col .groundNode).val := by
        intro heq
        have hlt := (col .groundNode).isLt
        have := Fin.val_add (col .groundNode) (1 : Fin 3)
        simp only [Fin.val_one] at this
        omega
      -- omega: three constraints (< 3, ≠ g, ≠ ct, ct ≠ g) uniquely pin the value
      constructor
      · apply Fin.ext
        have := (col .groundNode).isLt
        have := (col (.varNode c.v0)).isLt
        have := (col (.varNode c.v1)).isLt
        have := fun h => hg0 (Fin.ext h); have := fun h => hg1 (Fin.ext h)
        have := fun h => hf0 (Fin.ext h); have := fun h => hf1 (Fin.ext h)
        omega
      · apply Fin.ext
        have := (col .groundNode).isLt
        have := (col (.varNode c.v0)).isLt
        have := (col (.varNode c.v2)).isLt
        have := fun h => hg0 (Fin.ext h); have := fun h => hg2 (Fin.ext h)
        have := fun h => hf0 (Fin.ext h); have := fun h => hf2 (Fin.ext h)
        omega
  -- Now derive contradiction: 3 distinct clauseNode colors can't all avoid one var color
  obtain ⟨hcol01, hcol02⟩ := hSameColor
  have hVC0c := hVC0 c
  have hVC1c : col (.clauseNode c 1) ≠ col (.varNode c.v0) :=
    fun h => hVC1 c (h.trans hcol01)
  have hVC2c : col (.clauseNode c 2) ≠ col (.varNode c.v0) :=
    fun h => hVC2 c (h.trans hcol02)
  -- Three distinct Fin 3 values all ≠ x is impossible (pigeonhole)
  have cn0 := (col (.clauseNode c 0)).isLt
  have cn1 := (col (.clauseNode c 1)).isLt
  have cn2 := (col (.clauseNode c 2)).isLt
  have cvx := (col (.varNode c.v0)).isLt
  have ne01 : (col (.clauseNode c 0)).val ≠ (col (.clauseNode c 1)).val :=
    fun h => hCC c hcIn 0 1 (by decide) (Fin.ext h)
  have ne02 : (col (.clauseNode c 0)).val ≠ (col (.clauseNode c 2)).val :=
    fun h => hCC c hcIn 0 2 (by decide) (Fin.ext h)
  have ne12 : (col (.clauseNode c 1)).val ≠ (col (.clauseNode c 2)).val :=
    fun h => hCC c hcIn 1 2 (by decide) (Fin.ext h)
  have nex0 : (col (.clauseNode c 0)).val ≠ (col (.varNode c.v0)).val :=
    fun h => hVC0c (Fin.ext h)
  have nex1 : (col (.clauseNode c 1)).val ≠ (col (.varNode c.v0)).val :=
    fun h => hVC1c (Fin.ext h)
  have nex2 : (col (.clauseNode c 2)).val ≠ (col (.varNode c.v0)).val :=
    fun h => hVC2c (Fin.ext h)
  omega
