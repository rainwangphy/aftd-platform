import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueNoConflictOfTrue
import AFTD.Kb.Tcs.ThreeSATToCliqueGetLitAt
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueHasClique
import AFTD.Kb.Tcs.ThreeSATToCliqueCliqueVertex
import AFTD.Kb.Tcs.ThreeSATToCliqueIs3Satisfiable
import AFTD.Kb.Tcs.ThreeSATToCliqueEvalLiteral
import AFTD.Kb.Tcs.ThreeSATToCliqueToCliqueGraph
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteralsConflict
import AFTD.Kb.Tcs.ThreeSATToCliqueClause3Satisfied
import AFTD.Kb.Tcs.ThreeSATToCliqueClause3
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3Satisfied
import AFTD.Kb.Tcs.ThreeSATToCliqueAssignment

/-!
# ThreeSATToClique.ThreeSAT_to_Clique_completeness

Topic: np_completeness   Node: e96ac44a870a

Provenance: helper lemma. TCSlib, `ThreeSATToClique.ThreeSAT_to_Clique_completeness`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Completeness of the 3-SAT to clique reduction. Let $f$ be a 3-CNF formula consisting of $m$ clauses, and let its conflict graph be the
simple graph on the vertices $\langle c, \ell\rangle$ (clause index $c$, literal
position $\ell$) in which two vertices are adjacent exactly when they belong to
different clauses and their literals do not conflict. If $f$ is satisfiable, then this
conflict graph has an $m$-clique.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- **Completeness**: every satisfiable 3-CNF formula with `m` clauses has an `m`-clique in its conflict graph. *Proof*: from the satisfying assignment `α`, pick one true literal per clause (position `choice i` in clause `i`). The resulting `m` vertices are pairwise adjacent because they come from distinct clauses and no two true literals conflict (`no_conflict_of_true`). -/
theorem ThreeSATToClique.ThreeSAT_to_Clique_completeness {V : Type} (f : Formula3 V) :
    is3Satisfiable f → hasClique (toCliqueGraph f) f.length := by
  rintro ⟨α, hsat⟩
  -- For each clause i, choose a position j such that the j-th literal is true.
  have h_choice : ∀ (i : Fin f.length), ∃ (j : Fin 3),
      evalLiteral α (getLitAt f (CliqueVertex.mk i j)) := by
    intro i
    have hclause := hsat (f.get i) (List.get_mem f i)
    rcases hclause with (h1 | h2 | h3)
    · exact ⟨0, h1⟩
    · exact ⟨1, h2⟩
    · exact ⟨2, h3⟩
  let choice (i : Fin f.length) : Fin 3 := (h_choice i).choose
  have hchoice_spec : ∀ i, evalLiteral α (getLitAt f ⟨i, choice i⟩) :=
    fun i => (h_choice i).choose_spec
  -- The clique: one vertex per clause, at the chosen position.
  let vertices : Finset (CliqueVertex f.length) :=
    Finset.univ.image (fun (i : Fin f.length) => CliqueVertex.mk i (choice i))
  -- The map i ↦ ⟨i, choice i⟩ is injective, so |vertices| = m.
  have hcard : vertices.card = f.length := by
    have hinj : Function.Injective (fun (i : Fin f.length) => CliqueVertex.mk i (choice i)) := by
      intro i j h; injection h
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin f.length]
  -- Any two distinct vertices are adjacent: different clauses, no conflict.
  have hclique : (toCliqueGraph f).IsClique vertices := by
    intro u hu v hv hne
    simp only [Finset.mem_coe, vertices] at hu hv
    rcases Finset.mem_image.mp hu with ⟨i, -, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨j, -, rfl⟩
    have hci_ne : i ≠ j := fun heq => hne (by simp [heq])
    exact ⟨by simpa using hci_ne,
           no_conflict_of_true α _ _ (hchoice_spec i) (hchoice_spec j)⟩
  exact ⟨vertices, hcard, hclique⟩
