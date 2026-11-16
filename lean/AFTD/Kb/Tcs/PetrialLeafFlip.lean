import AFTD.Prelude

/-!
# petrial_leaf_flip

Topic: combinatorics   Node: 76bec198a96f

Provenance: helper lemma. Diagonal toggle in the leaf-elimination recurrence for OP-1239.

For vertices v and u and a vertex subset F, restrict F to the complement of v and toggle membership of u.
-/

noncomputable def petrial_leaf_flip {V : Type*} [Fintype V] [DecidableEq V] (v u : V) (F : Finset V) : Finset (({v}ᶜ : Set V)) := Finset.univ.filter (fun x => (x.1 ∈ F ∧ x.1 ≠ u) ∨ (x.1 ∉ F ∧ x.1 = u))
