import AFTD.Prelude

/-!
# complete_bipartite_one_isContained_of_adj

Topic: graphs   Node: 34eedcd1cca7

Provenance: helper lemma. helper for arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Lemma 2.3 (PR-280)

A vertex v with p distinct neighbours g(0), ..., g(p-1) in R gives a copy of the star K_{1,p} in R.
-/

theorem complete_bipartite_one_isContained_of_adj {V : Type*} (R : SimpleGraph V) (p : ℕ) (v : V)
    (g : Fin p → V) (hg : Function.Injective g) (hadj : ∀ j, R.Adj v (g j)) :
    (completeBipartiteGraph (Fin 1) (Fin p)).IsContained R := by
  refine ⟨⟨⟨Sum.elim (fun _ => v) g, ?_⟩, ?_⟩⟩
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> simp at hab ⊢
    · exact hadj b
    · exact (hadj a).symm
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> simp at hab ⊢
    · exact Subsingleton.elim a b
    · exact (hadj b).ne hab
    · exact (hadj a).ne hab.symm
    · exact hg hab
