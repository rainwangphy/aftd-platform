import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueAssignment
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteral
import AFTD.Kb.Tcs.ThreeSATToCliqueCliqueVerticesChooseOnePerClause
import AFTD.Kb.Tcs.ThreeSATToCliqueEvalLiteral
import AFTD.Kb.Tcs.ThreeSATToCliqueGetLitAt
import AFTD.Kb.Tcs.ThreeSATToCliqueGetLitAtMemClause
import AFTD.Kb.Tcs.ThreeSATToCliqueHasClique
import AFTD.Kb.Tcs.ThreeSATToCliqueIs3Satisfiable
import AFTD.Kb.Tcs.ThreeSATToCliqueToCliqueGraph
import AFTD.Kb.Tcs.V

/-!
# ThreeSATToClique.ThreeSAT_to_Clique_soundness

Topic: np_completeness   Node: 6d95e514c7b2

Provenance: helper lemma. TCSlib, `ThreeSATToClique.ThreeSAT_to_Clique_soundness`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Soundness of the 3-SAT to clique reduction. Let $f$ be a 3-CNF formula consisting of $m$ clauses. If the conflict graph of $f$ has
an $m$-clique, then $f$ is satisfiable.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- **Soundness**: an `m`-clique in the conflict graph yields a satisfying assignment for the 3-CNF formula. *Proof outline*: 1. By `clique_vertices_choose_one_per_clause`, each clause `i` has a unique representative vertex `uᵢ` in the clique. 2. Define `α v = True` if some clique vertex names `.pos v`, and `False` if some clique vertex names `.neg v` (the clique's non-conflict condition ensures this is consistent). 3. For each clause `i`, the literal at `uᵢ` is true under `α` and belongs to clause `i` by `getLitAt_mem_clause`, so the clause is satisfied. -/
theorem ThreeSATToClique.ThreeSAT_to_Clique_soundness {V : Type} (f : Formula3 V) :
    hasClique (toCliqueGraph f) f.length → is3Satisfiable f := by
  classical
  rintro ⟨s, hcard, hclique⟩
  have h_one_per_clause := clique_vertices_choose_one_per_clause f s hcard hclique
  -- α v is True iff some clique vertex names `.pos v`.
  let α : Assignment V := fun v =>
    if h : ∃ u ∈ s, getLitAt f u = .pos v then True
    else if h' : ∃ u ∈ s, getLitAt f u = .neg v then False
    else False
  -- Equivalent characterisation of α used throughout the proof.
  have hα_iff : ∀ v, α v ↔ ∃ u ∈ s, getLitAt f u = .pos v := by
    intro v
    change (if h : _ then True else _) ↔ _
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => trivial⟩
    · exact ⟨fun f => f.elim, fun hex => (h hex).elim⟩
    · exact ⟨fun f => f.elim, fun hex => (h hex).elim⟩
  -- Every literal at a clique vertex evaluates to true under α.
  have h_lit_true : ∀ u ∈ s, evalLiteral α (getLitAt f u) := by
    intro u hu
    cases hlit : getLitAt f u with
    | pos v =>
      simp only [evalLiteral]
      rw [hα_iff]
      exact ⟨u, hu, hlit⟩
    | neg v =>
      simp only [evalLiteral]
      rw [hα_iff]
      rintro ⟨u', hu', heq'⟩
      -- u and u' are both in the clique.  If u = u', then .neg v = .pos v.
      have hne : u ≠ u' := by
        intro heq; rw [heq] at hlit; rw [hlit] at heq'; cases heq'
      -- Otherwise u and u' are adjacent, but their literals conflict.
      have hadj := hclique (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hu') hne
      apply hadj.2
      rw [hlit, heq']
      rfl
  -- Build the satisfying assignment.
  refine ⟨α, ?_⟩
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
  obtain ⟨u, ⟨hu, hci⟩, _⟩ := h_one_per_clause i
  have hlit_true := h_lit_true u hu
  have hmem := getLitAt_mem_clause f u i hci
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with h | h | h
  · exact Or.inl (h ▸ hlit_true)
  · exact Or.inr (Or.inl (h ▸ hlit_true))
  · exact Or.inr (Or.inr (h ▸ hlit_true))
