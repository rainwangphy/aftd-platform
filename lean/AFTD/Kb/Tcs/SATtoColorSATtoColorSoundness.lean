import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorClause
import AFTD.Kb.Tcs.SATtoColorEdgeRelation
import AFTD.Kb.Tcs.SATtoColorIs3Colorable
import AFTD.Kb.Tcs.SATtoColorIsSatisfiable
import AFTD.Kb.Tcs.SATtoColorLiteral
import AFTD.Kb.Tcs.SATtoColorOutputVertex
import AFTD.Kb.Tcs.SATtoColorReductionGraph
import AFTD.Kb.Tcs.SATtoColorSat3
import AFTD.Kb.Tcs.SATtoColorSatisfiesClause
import AFTD.Kb.Tcs.SATtoColorSatisfiesLiteral
import AFTD.Kb.Tcs.SATtoColorSatisfiesSat3
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.SATtoColorSoundness

Topic: np_completeness   Node: 0b4655e23953

Provenance: helper lemma. TCSlib, `SATtoColor.SATtoColorSoundness`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Soundness of the 3-SAT to 3-colouring reduction. Let $f$ be a 3-SAT instance over a variable type $V$, that is, a list of clauses, each
clause a triple of literals (positive or negative occurrences of variables). If the
reduction graph $\mathrm{ReductionGraph}(f)$ admits a proper $3$-colouring, then $f$ is
satisfiable: there exists a Boolean assignment $\mathrm{assign} \colon V \to
\{\mathrm{true}, \mathrm{false}\}$ under which every clause of $f$ has at least one
literal evaluating to $\mathrm{true}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Soundness of reduction from 3-SAT to 3-Coloring. -/
lemma SATtoColor.SATtoColorSoundness {V : Type} (f : Sat3 V) :
  Is3Colorable (ReductionGraph f) → IsSatisfiable f := by
  intro ⟨⟨col, hcol⟩⟩
  simp only [SimpleGraph.top_adj] at hcol
  have colNe : ∀ {u v : OutputVertex V},
      u ≠ v → (EdgeRelation f u v ∨ EdgeRelation f v u) → col u ≠ col v :=
    fun hne hedge => hcol ⟨hne, hedge⟩
  have hP01 : col (.palette 0) ≠ col (.palette 1) := colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hP02 : col (.palette 0) ≠ col (.palette 2) := colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hP12 : col (.palette 1) ≠ col (.palette 2) := colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hLB : ∀ l : Literal V, col (.literalNode l) ≠ col (.palette 0) := fun l =>
    colNe (by simp) (Or.inr trivial)
  have hPN : ∀ x : V, col (.literalNode (.pos x)) ≠ col (.literalNode (.neg x)) := fun x =>
    colNe (by simp) (Or.inl rfl)
  have hG5B : ∀ c' : Clause V, col (.clauseGadget c' 5) ≠ col (.palette 0) := fun c' =>
    colNe (by simp) (Or.inl trivial)
  have hG5F : ∀ c' : Clause V, col (.clauseGadget c' 5) ≠ col (.palette 2) := fun c' =>
    colNe (by simp) (Or.inl trivial)
  let assign := fun v : V => decide (col (.literalNode (.pos v)) = col (.palette 1))
  have hLFT : ∀ l : Literal V, SatisfiesLiteral assign l = false →
      col (.literalNode l) ≠ col (.palette 1) := by
    intro l hl
    cases l with
    | pos v =>
      simp only [SatisfiesLiteral] at hl
      exact of_decide_eq_false hl
    | neg v =>
      simp only [SatisfiesLiteral] at hl
      have hav : col (.literalNode (.pos v)) = col (.palette 1) := by
        apply of_decide_eq_true
        cases h : assign v
        · exfalso; simp [h] at hl
        · exact h
      intro hcontra
      exact hPN v (hav.trans hcontra.symm)
  refine ⟨assign, ?_⟩
  simp only [SatisfiesSat3, List.all_eq_true]
  intro c hcIn
  by_contra hFalse
  have hSatF : SatisfiesClause assign c = false := by
    cases h : SatisfiesClause assign c with
    | true => exact absurd h hFalse
    | false => rfl
  simp only [SatisfiesClause] at hSatF
  have hl1F : SatisfiesLiteral assign c.l1 = false := by
    cases h : SatisfiesLiteral assign c.l1 <;> simp_all
  have hl2F : SatisfiesLiteral assign c.l2 = false := by
    cases h : SatisfiesLiteral assign c.l2 <;> simp_all
  have hl3F : SatisfiesLiteral assign c.l3 = false := by
    cases h : SatisfiesLiteral assign c.l3 <;> simp_all
  have hL1neT := hLFT c.l1 hl1F
  have hL2neT := hLFT c.l2 hl2F
  have hL3neT := hLFT c.l3 hl3F
  have hG5T : col (.clauseGadget c 5) = col (.palette 1) := by
    apply Fin.ext
    have i0 := (col (.clauseGadget c 5)).isLt
    have i1 := (col (.palette 0)).isLt
    have i2 := (col (.palette 1)).isLt
    have i3 := (col (.palette 2)).isLt
    have h1 : (col (.clauseGadget c 5)).val ≠ (col (.palette 0)).val := fun h => hG5B c (Fin.ext h)
    have h2 : (col (.clauseGadget c 5)).val ≠ (col (.palette 2)).val := fun h => hG5F c (Fin.ext h)
    have h3 : (col (.palette 0)).val ≠ (col (.palette 1)).val := fun h => hP01 (Fin.ext h)
    have h4 : (col (.palette 0)).val ≠ (col (.palette 2)).val := fun h => hP02 (Fin.ext h)
    have h5 : (col (.palette 1)).val ≠ (col (.palette 2)).val := fun h => hP12 (Fin.ext h)
    omega
  have hG01 : col (.clauseGadget c 0) ≠ col (.clauseGadget c 1) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inl ⟨rfl, rfl⟩⟩)
  have hG02 : col (.clauseGadget c 0) ≠ col (.clauseGadget c 2) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
  have hG12 : col (.clauseGadget c 1) ≠ col (.clauseGadget c 2) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
  have hG23 : col (.clauseGadget c 2) ≠ col (.clauseGadget c 3) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩)
  have hG34 : col (.clauseGadget c 3) ≠ col (.clauseGadget c 4) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)
  have hG35 : col (.clauseGadget c 3) ≠ col (.clauseGadget c 5) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩)
  have hG45 : col (.clauseGadget c 4) ≠ col (.clauseGadget c 5) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))⟩)
  have hL1G0 : col (.literalNode c.l1) ≠ col (.clauseGadget c 0) :=
    colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hL2G1 : col (.literalNode c.l2) ≠ col (.clauseGadget c 1) :=
    colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hL3G4 : col (.literalNode c.l3) ≠ col (.clauseGadget c 4) :=
    colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have vp0 := (col (.palette 0)).isLt;       have vp1 := (col (.palette 1)).isLt
  have vp2 := (col (.palette 2)).isLt
  have vg0 := (col (.clauseGadget c 0)).isLt; have vg1 := (col (.clauseGadget c 1)).isLt
  have vg2 := (col (.clauseGadget c 2)).isLt; have vg3 := (col (.clauseGadget c 3)).isLt
  have vg4 := (col (.clauseGadget c 4)).isLt; have vg5 := (col (.clauseGadget c 5)).isLt
  have vl1 := (col (.literalNode c.l1)).isLt; have vl2 := (col (.literalNode c.l2)).isLt
  have vl3 := (col (.literalNode c.l3)).isLt
  have hp01 : (col (.palette 0)).val ≠ (col (.palette 1)).val := fun h => hP01 (Fin.ext h)
  have hp02 : (col (.palette 0)).val ≠ (col (.palette 2)).val := fun h => hP02 (Fin.ext h)
  have hp12 : (col (.palette 1)).val ≠ (col (.palette 2)).val := fun h => hP12 (Fin.ext h)
  have hl1b : (col (.literalNode c.l1)).val ≠ (col (.palette 0)).val := fun h => hLB c.l1 (Fin.ext h)
  have hl2b : (col (.literalNode c.l2)).val ≠ (col (.palette 0)).val := fun h => hLB c.l2 (Fin.ext h)
  have hl3b : (col (.literalNode c.l3)).val ≠ (col (.palette 0)).val := fun h => hLB c.l3 (Fin.ext h)
  have hl1t : (col (.literalNode c.l1)).val ≠ (col (.palette 1)).val := fun h => hL1neT (Fin.ext h)
  have hl2t : (col (.literalNode c.l2)).val ≠ (col (.palette 1)).val := fun h => hL2neT (Fin.ext h)
  have hl3t : (col (.literalNode c.l3)).val ≠ (col (.palette 1)).val := fun h => hL3neT (Fin.ext h)
  have hl1g0 : (col (.literalNode c.l1)).val ≠ (col (.clauseGadget c 0)).val := fun h => hL1G0 (Fin.ext h)
  have hl2g1 : (col (.literalNode c.l2)).val ≠ (col (.clauseGadget c 1)).val := fun h => hL2G1 (Fin.ext h)
  have hl3g4 : (col (.literalNode c.l3)).val ≠ (col (.clauseGadget c 4)).val := fun h => hL3G4 (Fin.ext h)
  have hg01 : (col (.clauseGadget c 0)).val ≠ (col (.clauseGadget c 1)).val := fun h => hG01 (Fin.ext h)
  have hg02 : (col (.clauseGadget c 0)).val ≠ (col (.clauseGadget c 2)).val := fun h => hG02 (Fin.ext h)
  have hg12 : (col (.clauseGadget c 1)).val ≠ (col (.clauseGadget c 2)).val := fun h => hG12 (Fin.ext h)
  have hg23 : (col (.clauseGadget c 2)).val ≠ (col (.clauseGadget c 3)).val := fun h => hG23 (Fin.ext h)
  have hg34 : (col (.clauseGadget c 3)).val ≠ (col (.clauseGadget c 4)).val := fun h => hG34 (Fin.ext h)
  have hg35 : (col (.clauseGadget c 3)).val ≠ (col (.clauseGadget c 5)).val := fun h => hG35 (Fin.ext h)
  have hg45 : (col (.clauseGadget c 4)).val ≠ (col (.clauseGadget c 5)).val := fun h => hG45 (Fin.ext h)
  have hg5t : (col (.clauseGadget c 5)).val = (col (.palette 1)).val := congrArg Fin.val hG5T
  omega
