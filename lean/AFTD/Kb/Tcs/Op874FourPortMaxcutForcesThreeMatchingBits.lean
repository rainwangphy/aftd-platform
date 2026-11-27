import AFTD.Prelude

/-!
# op874_four_port_maxcut_forces_three_matching_bits

Topic: graphs   Node: f72dd86de38d

Provenance: helper lemma. Four-port maximum-cut enumeration for OP-874; experiment 42449.

The indicated four-port cut score forces three of the six internal matching bits.
-/

theorem op874_four_port_maxcut_forces_three_matching_bits :
  let L : Fin 26 → Fin 20 := ![0,0,0,1,1,2,2,3,4,4,4,5,5,6,7,8,8,9,10,10,11,12,12,13,14,15]
  let R : Fin 26 → Fin 20 := ![1,3,18,2,14,3,19,16,5,6,7,6,9,7,8,9,11,10,11,12,13,13,15,14,15,17]
  let ends : Fin 26 → Sym2 (Fin 20) := fun e => s(L e,R e)
  let M : Finset (Fin 26) := {19,20,12,14,4,9,7,25,2,6}
  let owner : Fin 20 → Fin 10 := ![8,4,9,6,5,2,5,3,3,2,0,1,0,1,4,7,6,7,8,9]
  let port : Fin 4 → Fin 20 := ![3,15,0,2]
  let portEdge : Fin 4 → Fin 26 := ![7,25,2,6]
  ∀ B : Fin 6 → Bool,
    let allBits : Fin 10 → Bool := ![B 0,B 1,B 2,B 3,B 4,B 5,false,true,false,true]
    let bit : Fin 20 → Bool := fun v => allBits (owner v)
    ((Finset.univ : Finset (Fin 26)).filter fun e => e ∉ M ∧ bit (L e) ≠ bit (R e)).card = 12 →
    B 0 = false ∧ B 1 = true ∧ B 4 = false := by
  set_option maxHeartbeats 4000000 in
    decide
