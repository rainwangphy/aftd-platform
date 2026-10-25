import AFTD.Prelude

/-!
# cyclic_four_block_graph

Topic: graphs   Node: cafe9d79a565

Provenance: helper lemma. Explicit indexed helper family for OP-309: an odd cyclic four-vertex-block representation of the standard cubic flower family; see arXiv:2306.13340 for related normal five-edge-colorings. Vertex labels here are b_i=4i,a_i=4i+1,c_i=4i+2,d_i=4i+3. Used as a concrete partial case of OP-309.

For n=2m+5, the graph has vertices b_i,a_i,c_i,d_i and edges b_i-a_i,b_i-c_i,b_i-d_i,a_i-a_next. The c and d strands run forward separately until their crossed wraparound joins c_last-d_0 and d_last-c_0.
-/

def cyclic_four_block_graph (m : ℕ) : SimpleGraph (Fin (4*(2*m+5))) :=
  let n := 2*m+5
  let next : Fin n → ℕ := fun i => if i.val+1<n then i.val+1 else 0
  let src : Fin n × Fin 6 → ℕ := fun e => 4*e.1.val + ![0,0,0,1,2,3] e.2
  let dst : Fin n × Fin 6 → ℕ := fun e =>
    ![4*e.1.val+1,4*e.1.val+2,4*e.1.val+3,4*next e.1+1,
      if e.1.val+1=n then 3 else 4*(e.1.val+1)+2,
      if e.1.val+1=n then 2 else 4*(e.1.val+1)+3] e.2
  SimpleGraph.fromEdgeSet (Set.range (fun e : Fin n × Fin 6 =>
    s(⟨src e,by
        rcases e with ⟨i,j⟩
        fin_cases j <;> dsimp [src,n] <;> omega⟩,
      ⟨dst e,by
        rcases e with ⟨i,j⟩
        fin_cases j <;> dsimp [dst,next,n]
        all_goals (try split_ifs) <;> omega⟩)))
