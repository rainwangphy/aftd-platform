import AFTD.Prelude
import AFTD.Kb.Tcs.Op2378PetersenEdges

/-!
# op_2378_is_perfect_matching

Topic: graphs   Node: 4a4b44520840

Provenance: helper lemma. step towards op_2378_partial_r_two

A Finset of edges of a graph G on Fin 10 is a perfect matching if all its members are edges of G and every vertex is incident with exactly one of its members.
-/

/-- Perfect matchings of a graph on Fin 10, in a form that is decidable and enumerable. -/
def op_2378_is_perfect_matching (G : SimpleGraph (Fin 10)) (M : Finset (Sym2 (Fin 10))) : Prop := (↑M : Set (Sym2 (Fin 10))) ⊆ G.edgeSet ∧
     ∀ v : Fin 10, (M.filter (fun e => v ∈ (e : Sym2 (Fin 10)))).card = 1
