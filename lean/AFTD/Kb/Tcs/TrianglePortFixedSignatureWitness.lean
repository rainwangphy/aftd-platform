import AFTD.Prelude

/-!
# triangle_port_fixed_signature_witness

Topic: combinatorics   Node: 1055a9369b5e

Provenance: helper lemma. Finite port-signature obstruction investigated for OP-874; local compatibility appears in arXiv:2610.41950, Section 2.

The explicitly indexed 15-edge augmented truncation of a triangle three-port piece has a strong six-edge-coloring whose boundary external colors are 0, 1, 2 and whose exposed color pairs are respectively {1,2}, {0,2}, {0,1}.
-/

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def triangle_port_obstruction_edge (i : Fin 15) : Fin 12 × Fin 12 :=
  ![(0,1),(0,2),(0,3),(1,2),(1,6),(2,9),
    (3,4),(3,5),(4,5),(4,7),(5,10),
    (6,7),(6,8),(7,8),(8,11)] i

def triangle_port_obstruction_color (i : Fin 15) : Fin 6 :=
  ![3,1,4,2,5,0, 5,0,2,3,1, 4,0,1,2] i

def triangle_port_obstruction_adj (u v : Fin 12) : Prop :=
  ∃ i : Fin 15, triangle_port_obstruction_edge i = (u,v) ∨ triangle_port_obstruction_edge i = (v,u)

def triangle_port_obstruction_conflict (i j : Fin 15) : Prop :=
  let a := (triangle_port_obstruction_edge i).1; let b := (triangle_port_obstruction_edge i).2
  let c := (triangle_port_obstruction_edge j).1; let d := (triangle_port_obstruction_edge j).2
  a = c ∨ a = d ∨ b = c ∨ b = d ∨
  triangle_port_obstruction_adj a c ∨ triangle_port_obstruction_adj a d ∨ triangle_port_obstruction_adj b c ∨ triangle_port_obstruction_adj b d

instance (u v : Fin 12) : Decidable (triangle_port_obstruction_adj u v) := by
  unfold triangle_port_obstruction_adj
  infer_instance

instance (i j : Fin 15) : Decidable (triangle_port_obstruction_conflict i j) := by
  unfold triangle_port_obstruction_conflict
  infer_instance

theorem triangle_port_fixed_signature_witness :
    (∀ i j : Fin 15, i ≠ j → triangle_port_obstruction_conflict i j → triangle_port_obstruction_color i ≠ triangle_port_obstruction_color j) ∧
    triangle_port_obstruction_color 5 = 0 ∧ triangle_port_obstruction_color 1 = 1 ∧ triangle_port_obstruction_color 3 = 2 ∧
    triangle_port_obstruction_color 10 = 1 ∧ triangle_port_obstruction_color 7 = 0 ∧ triangle_port_obstruction_color 8 = 2 ∧
    triangle_port_obstruction_color 14 = 2 ∧ triangle_port_obstruction_color 12 = 0 ∧ triangle_port_obstruction_color 13 = 1 := by decide
