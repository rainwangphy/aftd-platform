import AFTD.Prelude

/-!
# op874_saturated_twenty_four_data

Topic: graphs   Node: 1b547b45c814

Provenance: helper lemma. Finite graph certificate for the OP-874 cycle-color obstruction, https://arxiv.org/abs/2610.41950.

A specified 24-vertex simple cubic edge set has the displayed Hamiltonian cycle, perfect matching and four complementary cycles of lengths 5, 5, 6 and 8; both odd cycles are mixed and every matching edge meets the local-cut constraint with equality. The Hamiltonian cycle also certifies connectedness and absence of bridges.
-/

theorem op874_saturated_twenty_four_data :
    let E : Finset (Sym2 (Fin 24)) := {s((0 : Fin 24),1),s((0 : Fin 24),4),s((0 : Fin 24),9),s((1 : Fin 24),2),s((1 : Fin 24),22),s((2 : Fin 24),3),s((2 : Fin 24),13),s((3 : Fin 24),4),s((3 : Fin 24),11),s((4 : Fin 24),6),s((5 : Fin 24),6),s((5 : Fin 24),9),s((5 : Fin 24),15),s((6 : Fin 24),7),s((7 : Fin 24),8),s((7 : Fin 24),14),s((8 : Fin 24),9),s((8 : Fin 24),12),s((10 : Fin 24),11),s((10 : Fin 24),15),s((10 : Fin 24),19),s((11 : Fin 24),12),s((12 : Fin 24),13),s((13 : Fin 24),14),s((14 : Fin 24),15),s((16 : Fin 24),17),s((16 : Fin 24),20),s((16 : Fin 24),23),s((17 : Fin 24),18),s((17 : Fin 24),21),s((18 : Fin 24),19),s((18 : Fin 24),23),s((19 : Fin 24),20),s((20 : Fin 24),21),s((21 : Fin 24),22),s((22 : Fin 24),23)}
    let M : Finset (Sym2 (Fin 24)) := {s((4 : Fin 24),6),s((0 : Fin 24),9),s((17 : Fin 24),21),s((8 : Fin 24),12),s((16 : Fin 24),20),s((3 : Fin 24),11),s((5 : Fin 24),15),s((7 : Fin 24),14),s((18 : Fin 24),23),s((10 : Fin 24),19),s((2 : Fin 24),13),s((1 : Fin 24),22)}
    let bit : Fin 24 → Bool := ![false,true,true,false,false,true,false,true,false,false,true,false,false,true,true,true,false,false,true,true,false,false,true,true]
    let P : Fin 24 → Fin 24 := ![0,1,22,21,17,18,23,16,20,19,10,11,12,13,2,3,4,6,5,15,14,7,8,9]
    let A : Fin 5 → Fin 24 := ![0,1,2,3,4]
    let B : Fin 5 → Fin 24 := ![5,6,7,8,9]
    let C : Fin 6 → Fin 24 := ![10,11,12,13,14,15]
    let D : Fin 8 → Fin 24 := ![16,17,18,19,20,21,22,23]
    let F : Finset (Sym2 (Fin 24)) :=
      Finset.univ.image (fun i : Fin 5 => s(A i,A (i+1))) ∪
      Finset.univ.image (fun i : Fin 5 => s(B i,B (i+1))) ∪
      Finset.univ.image (fun i : Fin 6 => s(C i,C (i+1))) ∪
      Finset.univ.image (fun i : Fin 8 => s(D i,D (i+1)))
    let same : Fin 24 → ℕ := fun v => (F.filter fun e =>
      ∃ w : Fin 24, e = s(v,w) ∧ bit v = bit w).card
    (∀ e ∈ E, ¬ e.IsDiag) ∧
    (∀ v : Fin 24, (E.filter fun e => v ∈ e).card = 3) ∧
    Function.Injective P ∧ (∀ i : Fin 24, s(P i,P (i+1)) ∈ E) ∧
    M ⊆ E ∧ (∀ v : Fin 24, (M.filter fun e => v ∈ e).card = 1) ∧
    E = F ∪ M ∧ Disjoint F M ∧
    (∀ u v : Fin 24, s(u,v) ∈ M → bit u = bit v ∧ same u + same v = 2) ∧
    bit (A 0) ≠ bit (A 1) ∧ bit (B 0) ≠ bit (B 1) := by
  decide
