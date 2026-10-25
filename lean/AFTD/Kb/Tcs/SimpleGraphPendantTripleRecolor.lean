import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPendantTripleExpand

/-!
# simple_graph_pendant_triple_recolor

Topic: graphs   Node: 7a89f8275c4c

Provenance: helper lemma. step towards simple_graph_rich_neighbor_five_pendant_triple_extend

The edge-colour function of the pendant-triple expansion attached to a colouring `f` of all vertex pairs of `G`: an edge coming from an old edge keeps its colour, the two new end edges `u-0` and `2-v` both get `x`, the new path edges `0-1` and `1-2` get `y` and `z`, and the three pendant edges `03`, `14`, `25` get `A`, `B`, `C`.
-/

/-- Edge colour function for the triple expansion: old edges keep the colour `f`, the end edges `u-0`,`2-v` get `x`, the paths edges `0-1`,`1-2` get `y`,`z`, the pendants `03`,`14`,`25` get `A`,`B`,`C`. -/
noncomputable def simple_graph_pendant_triple_recolor {V : Type*} (G : SimpleGraph V) (u v : V)
    (f : Sym2 V → Fin 5) (x y z A B C : Fin 5) :
    (simple_graph_pendant_triple_expand G u v).edgeSet → Fin 5 := fun E => by
    classical
    exact
      if h : (E : Sym2 (V ⊕ Fin 6)) ∈ Set.range (Sym2.map Sum.inl) then f (Classical.choose h)
      else if (E : Sym2 (V ⊕ Fin 6)) = s(Sum.inl u, Sum.inr 0) then x
      else if (E : Sym2 (V ⊕ Fin 6)) = s(Sum.inr 0, Sum.inr 1) then y
      else if (E : Sym2 (V ⊕ Fin 6)) = s(Sum.inr 1, Sum.inr 2) then z
      else if (E : Sym2 (V ⊕ Fin 6)) = s(Sum.inr 2, Sum.inl v) then x
      else if (E : Sym2 (V ⊕ Fin 6)) = s(Sum.inr 0, Sum.inr 3) then A
      else if (E : Sym2 (V ⊕ Fin 6)) = s(Sum.inr 1, Sum.inr 4) then B
      else if (E : Sym2 (V ⊕ Fin 6)) = s(Sum.inr 2, Sum.inr 5) then C
      else x
