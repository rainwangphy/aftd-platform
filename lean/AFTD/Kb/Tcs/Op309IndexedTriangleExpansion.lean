import AFTD.Prelude

/-!
# op309_indexed_triangle_expansion

Topic: graphs   Node: b14635ff91f8

Provenance: helper lemma. OP-309 triangle expansion bounded recoloring route

Replace vertex zero by a triangle while retaining all old edge indices, with the three specified spoke indices rewired to the triangle vertices.
-/

def op309_indexed_triangle_expansion{n m : ℕ} (hn : 4 ≤ n)
    (E : Fin m → Fin n × Fin n) : Fin (m+3) → Fin (n+2) × Fin (n+2) := fun i =>
  if i.val=0 then (⟨0,by omega⟩,⟨1,by omega⟩)
  else if i.val=1 then (⟨n,by omega⟩,⟨2,by omega⟩)
  else if i.val=2 then (⟨n+1,by omega⟩,⟨3,by omega⟩)
  else if h : i.val < m then
    let e := E ⟨i.val,h⟩
    (e.1.castAdd 2,e.2.castAdd 2)
  else if i.val=m then (⟨0,by omega⟩,⟨n,by omega⟩)
  else if i.val=m+1 then (⟨n,by omega⟩,⟨n+1,by omega⟩)
  else (⟨n+1,by omega⟩,⟨0,by omega⟩)
