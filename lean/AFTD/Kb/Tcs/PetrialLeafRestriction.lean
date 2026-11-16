import AFTD.Prelude

/-!
# petrial_leaf_restriction

Topic: combinatorics   Node: 2a7877ce5357

Provenance: helper lemma. Auxiliary definition for the partial Petrial leaf recurrence.

Restrict a finite vertex subset to the complement of vertices u and v.
-/

noncomputable def petrial_leaf_restriction {V : Type*} [Fintype V] [DecidableEq V] (v u : V) (F : Finset V) : Finset (({u, v}ᶜ : Set V)) := Finset.univ.filter (fun x => x.1 ∈ F)
