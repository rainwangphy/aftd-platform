import AFTD.Prelude
import AFTD.Kb.Tcs.Bicirculant3465ColumnCycle

/-!
# bicirculant_3465_ham_vertices

Topic: graphs   Node: 2ae117153286

Provenance: helper lemma. step towards op_1151_bicirculant_3465_is_hamiltonian

Explicit enumeration of all 6930 vertices of the bicirculant graph: index j = 6*i + p walks the 1155 columns in `bicirculant_3465_column_cycle` order; in column i (the six vertices (L, (column i).val + 1155*k)) it lists the triangular-prism Hamiltonian path from the layer-0 vertex (0, x) to the layer-1 vertex (1, x + 1155*carry), where carry = 1 iff (column i).val < step(i).
-/

def bicirculant_3465_ham_vertices (j : Fin 6930) : Fin 2 × ZMod 3465 := let i : Fin 1155 := ⟨j.val / 6, by omega⟩
   let c : ℕ := (bicirculant_3465_column_cycle i).val
   let x : ZMod 3465 := (c : ZMod 3465)
   let d : ℕ := if i.val % 3 = 0 then 35 else if i.val % 3 = 1 then 77 else 275
   let e : ℕ := if c < d then 1 else 0
   let p : ℕ := j.val % 6
   if e = 0 then
     (if p = 0 then ((0 : Fin 2), x) else if p = 1 then (0, x + 1155) else if p = 2 then (0, x + 2310)
      else if p = 3 then (1, x + 2310) else if p = 4 then (1, x + 1155) else (1, x))
   else
     (if p = 0 then ((0 : Fin 2), x) else if p = 1 then (0, x + 1155) else if p = 2 then (0, x + 2310)
      else if p = 3 then (1, x + 2310) else if p = 4 then (1, x) else (1, x + 1155))
